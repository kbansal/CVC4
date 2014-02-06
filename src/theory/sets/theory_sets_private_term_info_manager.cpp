#include "theory/sets/theory_sets_private.h"
#include "theory/sets/expr_patterns.h"

using namespace CVC4::expr::pattern;

namespace CVC4 {
namespace theory {
namespace sets {

void TheorySetsPrivate::TermInfoManager::mergeLists
(CDTNodeList* la, const CDTNodeList* lb) const {
  // straight from theory/arrays/array_info.cpp
  std::set<TNode> temp;
  CDTNodeList::const_iterator it;
  for(it = la->begin() ; it != la->end(); it++ ) {
    temp.insert((*it));
  }

  for(it = lb->begin() ; it!= lb->end(); it++ ) {
    if(temp.count(*it) == 0) {
      la->push_back(*it);
    }
  }
}

TheorySetsPrivate::TermInfoManager::TermInfoManager
(TheorySetsPrivate& theory, context::Context* satContext, eq::EqualityEngine* eq):
  d_theory(theory),
  d_context(satContext),
  d_eqEngine(eq),
  d_terms(satContext),
  d_info()
{ }

TheorySetsPrivate::TermInfoManager::~TermInfoManager() {
  for( typeof(d_info.begin()) it = d_info.begin();
       it != d_info.end(); ++it) {
    delete (*it).second;
  }
}

void TheorySetsPrivate::TermInfoManager::notifyMembership(TNode fact) {
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];

  TNode x = d_eqEngine->getRepresentative(atom[0]);
  TNode S = d_eqEngine->getRepresentative(atom[1]);

  Debug("sets-terminfo") << "[sets-terminfo] Adding membership " << x
                         << " in " << S << " " << polarity << std::endl;

  Node atomModEq = IN(x, S);
  if(!d_eqEngine->hasTerm(atomModEq)) {
    d_eqEngine->addTerm(atomModEq);

#if CVC4_ASSERTIONS
    // Make sure the predicate modulo equalities already holds
    Node polarity_atom = NodeManager::currentNM()->mkConst<bool>(polarity);
    Assert(d_eqEngine->areEqual(atomModEq, polarity_atom));
#endif
  }

  // d_info[x]->addToSetList(S, polarity);
  d_info[S]->addToElementList(x, polarity);
}

CDTNodeList* TheorySetsPrivate::TermInfoManager::getParents(TNode x) {
  return d_info[x]->parents;
}

void TheorySetsPrivate::TermInfoManager::addTerm(TNode n) {
  unsigned numChild = n.getNumChildren();

  if(!d_terms.contains(n)) {
    d_terms.insert(n);
    d_info[n] = new TheorySetsTermInfo(n, d_context);
  }

  if(n.getKind() == kind::UNION ||
     n.getKind() == kind::INTERSECTION ||
     n.getKind() == kind::SETMINUS || 
     n.getKind() == kind::SET_SINGLETON) {

    for(unsigned i = 0; i < numChild; ++i) {
      if(d_terms.contains(n[i])) {
        Debug("sets-parent") << "Adding " << n << " to parent list of "
                             << n[i] << std::endl;
        d_info[n[i]]->parents->push_back(n);
      }
    }

  }
}

void TheorySetsPrivate::TermInfoManager::pushToSettermPropagationQueue
(CDTNodeList* l, TNode S, bool polarity)
{
  for(typeof(l->begin()) i = l->begin(); i != l->end(); ++i) {
    Debug("sets-prop") << "[sets-terminfo]  setterm todo: " 
                       << IN(*i, d_eqEngine->getRepresentative(S))
                       << std::endl;
    d_eqEngine->addTerm(IN(d_eqEngine->getRepresentative(*i),
                           d_eqEngine->getRepresentative(S)));
    // d_theory.registerReason(IN(*i, d_eqEngine->getRepresentative(S)), false);
    for(eq::EqClassIterator j(d_eqEngine->getRepresentative(S), d_eqEngine);
        !j.isFinished(); ++j) {

      TNode x = (*i);
      TNode S = (*j);
      Node cur_atom = IN(x, S);

      // propagation : empty set
      if(polarity && S.getKind() == kind::EMPTYSET) {
        Debug("sets-prop") << "[sets-prop]  something in empty set? conflict."
                           << std::endl;
        d_theory.learnLiteral(cur_atom, false, cur_atom);
        //Assert(d_theory.d_conflict);
        return;
      }// propagation: empty set

      // propagation : children
      // Debug("sets-prop") << "[sets-prop] Propagating 'down' for "
      //                    << x << element_of_str << S << std::endl;
      if(S.getKind() == kind::UNION ||
         S.getKind() == kind::INTERSECTION ||
         S.getKind() == kind::SETMINUS ||
         S.getKind() == kind::SET_SINGLETON) {
        d_theory.d_settermPropagationQueue.push_back(std::make_pair(x, S));
      }// propagation: children

      // propagation : parents
      // Debug("sets-prop") << "[sets-prop] Propagating 'up' for "
      //                    << x << element_of_str << S << std::endl;
      CDTNodeList* parentList = getParents(S);
      for(typeof(parentList->begin()) k = parentList->begin();
          k != parentList->end(); ++k) {
        d_theory.d_settermPropagationQueue.push_back(std::make_pair(x, *k));
      }// propagation : parents


    }//j loop

  }
    
}

void TheorySetsPrivate::TermInfoManager::mergeTerms(TNode a, TNode b) {
  // merge b into a
  if(!a.getType().isSet()) return;

  Debug("sets-terminfo") << "[sets-terminfo] Merging (into) a = " << a
                         << ", b = " << b << std::endl;
  Debug("sets-terminfo") << "[sets-terminfo] reps a: " << d_eqEngine->getRepresentative(a)
                         << ", b: " << d_eqEngine->getRepresentative(b) << std::endl;

  typeof(d_info.begin()) ita = d_info.find(a);
  typeof(d_info.begin()) itb = d_info.find(b);

  Assert(ita != d_info.end());
  Assert(itb != d_info.end());
    
  // learnt: (elements <a> contains) now also in <b>
  pushToSettermPropagationQueue( (*ita).second->elementsInThisSet, b, true );
  pushToSettermPropagationQueue( (*ita).second->elementsNotInThisSet, b, false );
  pushToSettermPropagationQueue( (*itb).second->elementsNotInThisSet, a, false );
  pushToSettermPropagationQueue( (*itb).second->elementsInThisSet, a, true );

  mergeLists((*ita).second->inThisEqClass,
             (*itb).second->inThisEqClass);

  mergeLists((*ita).second->elementsInThisSet,
             (*itb).second->elementsInThisSet);

  mergeLists((*ita).second->elementsNotInThisSet,
             (*itb).second->elementsNotInThisSet);

  mergeLists((*ita).second->setsThisElementIsIn,
             (*itb).second->setsThisElementIsIn);

  mergeLists((*ita).second->setsThisElementIsNotIn,
             (*itb).second->setsThisElementIsNotIn);
}


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
