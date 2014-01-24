#include "theory/sets/theory_sets.h"
#include "theory/sets/theory_sets_private.h"
#include "util/result.h"
#include "theory/sets/expr_patterns.h" // ONLY included here

using namespace std;
using namespace CVC4::expr::pattern;

namespace CVC4 {
namespace theory {
namespace sets {

const char* element_of_str = " \u2208 ";

/********************** Term information ***************************/
/********************** Term information ***************************/
/********************** Term information ***************************/


/** Begin: adapted from theory/arrays/info.cpp */
typedef context::CDList<TNode> CDTNodeList;
typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;
typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;

class TheorySetsTermInfo {
  TNode d_term;                 // actually unnecessary since we
                                // maintain the invariant that
                                // inThisEqClass' first element will
                                // be d_term
public:
  CDTNodeList* inThisEqClass;
  CDTNodeList* elementsInThisSet;
  CDTNodeList* elementsNotInThisSet;
  CDTNodeList* setsThisElementIsIn;
  CDTNodeList* setsThisElementIsNotIn;
  CDTNodeList* parents;
  TheorySetsTermInfo(TNode t, context::Context* c):
    d_term(t)
  {
    Debug("sets-terminfo") << "[sets-terminfo] Creating info for " << d_term
                           << std::endl;

    inThisEqClass = new(true)CDTNodeList(c);
    elementsInThisSet = new(true)CDTNodeList(c);
    elementsNotInThisSet = new(true)CDTNodeList(c);
    setsThisElementIsIn = new(true)CDTNodeList(c);
    setsThisElementIsNotIn = new(true)CDTNodeList(c);
    parents = new(true)CDTNodeList(c);

    inThisEqClass->push_back(t);
  }

  void addToSetList(TNode n, bool polarity) {
    if(polarity) setsThisElementIsIn -> push_back(n);
    else setsThisElementIsNotIn -> push_back(n);
  }
  void addToElementList(TNode n, bool polarity) {
    if(polarity) elementsInThisSet -> push_back(n);
    else elementsNotInThisSet -> push_back(n);
  }

  ~TheorySetsTermInfo() {
    Debug("sets-terminfo") << "[sets-terminfo] Destroying info for " << d_term
                           << std::endl;

    inThisEqClass -> deleteSelf();
    elementsInThisSet -> deleteSelf();
    elementsNotInThisSet -> deleteSelf();
    setsThisElementIsIn -> deleteSelf();
    setsThisElementIsNotIn -> deleteSelf();
    parents -> deleteSelf();
  }
};
/** End: adapted from theory/arrays/array_info.cpp */

class TheorySetsTermInfoManager {

  CDNodeSet d_terms;
  hash_map<TNode, TheorySetsTermInfo*, TNodeHashFunction> d_info;

  context::Context* d_context;

  eq::EqualityEngine* d_eqEngine;

  void mergeLists(CDTNodeList* la, const CDTNodeList* lb) const{
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

public:
  TheorySetsTermInfoManager(context::Context* sc,
                            eq::EqualityEngine* eq):
    d_terms(sc),
    d_context(sc),
    d_eqEngine(eq)
  { }

  ~TheorySetsTermInfoManager() {
    for( typeof(d_info.begin()) it = d_info.begin();
         it != d_info.end(); ++it) {
      delete (*it).second;
    }
  }

  void notifyMembership(TNode fact) {
    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    TNode x = d_eqEngine->getRepresentative(atom[0]);
    TNode S = d_eqEngine->getRepresentative(atom[1]);

    Debug("sets-terminfo") << "[sets-terminfo] Adding membership " << x
                           << " in " << S << " " << polarity << std::endl;

    Node atomModEq = IN(x, S);
    if(!d_eqEngine->hasTerm(atomModEq)) {
      d_eqEngine->addTriggerPredicate(atomModEq);

#if CVC4_ASSERTIONS
    // Make sure the predicate modulo equalities already holds
    Node polarity_atom = NodeManager::currentNM()->mkConst<bool>(polarity);
    Assert(d_eqEngine->areEqual(atomModEq, polarity_atom));
#endif
    }


    d_info[x]->addToSetList(S, polarity);
    d_info[S]->addToElementList(x, polarity);
  }

  CDTNodeList* getParents(TNode x) {
    return d_info[x]->parents;
  }

  void addTerm(TNode n) {
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

  void mergeTerms(TNode a, TNode b) {
    // merge b into a

    Debug("sets-terminfo") << "[sets-terminfo] Merging (into) a = " << a
                           << ", b = " << b << std::endl;

    typeof(d_info.begin()) ita = d_info.find(a);
    typeof(d_info.begin()) itb = d_info.find(b);

    Assert(ita != d_info.end());
    Assert(itb != d_info.end());

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
         
};



/********************** Helper functions ***************************/
/********************** Helper functions ***************************/
/********************** Helper functions ***************************/

Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  for (unsigned i = 0; i < conjunctions.size(); ++i) {
    TNode t = conjunctions[i];
    if (t.getKind() == kind::AND) {
      for(TNode::iterator child_it = t.begin();
          child_it != t.end(); ++child_it) {
        all.insert(*child_it);
      }
    }
    else {
      all.insert(t);
    }
  }

  Assert(all.size() > 0);

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */




/********************** TheorySetsPrivate::*() ***************************/
/********************** TheorySetsPrivate::*() ***************************/
/********************** TheorySetsPrivate::*() ***************************/

bool  TheorySetsPrivate::present(TNode atom) {
  Assert(atom.getKind() == kind::IN);
  return holds(atom) || holds(atom.notNode());
  // Node atom_rep = IN( d_equalityEngine.getRepresentative(atom[0]),
  //                     d_equalityEngine.getRepresentative(atom[1]) );
  // return d_assertions.find(atom_rep) != d_assertions.end();
}
bool TheorySetsPrivate::holds(TNode atom, bool polarity) {
  Node polarity_atom = NodeManager::currentNM()->mkConst<bool>(polarity);
  Node atomModEq = IN( d_equalityEngine.getRepresentative(atom[0]),
                  d_equalityEngine.getRepresentative(atom[1]) );
  return 
    d_equalityEngine.hasTerm(atomModEq) &&
    d_equalityEngine.areEqual(atomModEq, polarity_atom);
}

void TheorySetsPrivate::assertEquality(TNode fact, TNode reason, bool learnt)
{
  Assert(learnt == false);

  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];

  d_equalityEngine.assertEquality(atom, polarity, fact);
}

void TheorySetsPrivate::assertMemebership(TNode fact, TNode reason, bool learnt)
{
  Debug("sets-mem") << "\n[sets-mem] adding ( " << fact
                    << ", " << reason
                    << ", " << learnt << std::endl;

  bool polarity = fact.getKind() == kind::NOT ? false : true;
  TNode atom = polarity ? fact : fact[0];

  // fact already holds
  if( holds(atom, polarity) ) {
    Debug("sets-mem") << "[sets-mem]   already present, skipping" << std::endl;
    return;
  }

  // assert fact & check for conflict
  if(learnt) {
    registerReason(reason, true);
  }
  d_equalityEngine.assertPredicate(atom, polarity, reason);

  if(!d_equalityEngine.consistent()) {
    Debug("sets-mem") << "[sets-mem]   running into a conflict" << std::endl;
    d_conflict = true;
    return;
  }

  // update term info data structures
  d_termInfoManager->notifyMembership(fact);

  // propagation
  for(eq::EqClassIterator i(d_equalityEngine.getRepresentative(atom[0]), 
                            &d_equalityEngine); !i.isFinished(); ++i) {

    for(eq::EqClassIterator j(d_equalityEngine.getRepresentative(atom[1]),
                              &d_equalityEngine); !j.isFinished(); ++j) {

      TNode x = (*i);
      TNode S = (*j);
      Node cur_atom = IN(x, S);


      // propagation : empty set
      if(polarity && S.getKind() == kind::EMPTYSET) {
        Debug("sets-prop") << "[sets-prop]  something in empty set? conflict."
                           << std::endl;
        learnLiteral(cur_atom, false, cur_atom);
        Assert(d_conflict);
        return;
      }// propagation: empty set


      // propagation : children
      Debug("sets-prop") << "[sets-prop] Propagating 'down' for "
                         << x << element_of_str << S << std::endl;
      if(S.getKind() == kind::UNION ||
         S.getKind() == kind::INTERSECTION ||
         S.getKind() == kind::SETMINUS) {
        doSettermPropagation(x, S);
        if(d_conflict) return;
      }// propagation: children


      // propagation : parents
      Debug("sets-prop") << "[sets-prop] Propagating 'up' for "
                         << x << element_of_str << S << std::endl;
      CDTNodeList* parentList = d_termInfoManager->getParents(S);
      for(typeof(parentList->begin()) k = parentList->begin();
          k != parentList->end(); ++k) {
        doSettermPropagation(x, *k);
        if(d_conflict) return;
      }// propagation : parents


    }//j loop
  }//i loop

}

void
TheorySetsPrivate::doSettermPropagation(TNode x, TNode S)
{
  Debug("sets-prop") << "[sets-prop] doSettermPropagation("
                     << x << ", " << S << std::endl;

  Assert(S.getType().isSet() && S.getType().getSetElementType() == x.getType());

  Node literal, left_literal, right_literal;

  // axiom: literal <=> left_literal ^ right_literal
  switch(S.getKind()) {
  case kind::INTERSECTION:
    literal       =       IN(x, S)      ;
    left_literal  =       IN(x, S[0])   ; 
    right_literal =       IN(x, S[1])   ;
    break;
  case kind::UNION:
    literal       = NOT(  IN(x, S)     );
    left_literal  = NOT(  IN(x, S[0])  );
    right_literal = NOT(  IN(x, S[1])  );
    break;
  case kind::SETMINUS:
    literal       =       IN(x, S)      ;
    left_literal  =       IN(x, S[0])   ;
    right_literal = NOT(  IN(x, S[1])  );
    break;
  case kind::SET_SINGLETON:
    if(not (x == S[0] && holds(IN(x, S)))) {
      learnLiteral(EQUAL(x, S[0]), true, IN(x, S));
    }
    return;
  default:
    Unhandled();
  }

  Assert( present( IN(x, S)    ) || 
          present( IN(x, S[0]) ) || 
          present( IN(x, S[1]) ) );

  if( holds(literal) ) {
    // 1a. literal => left_literal
    Debug("sets-prop") << "[sets-prop]  ... via case 1a. ..." << std::endl;
    learnLiteral(left_literal, literal);
    if(d_conflict) return;

    // 1b. literal => right_literal
    Debug("sets-prop") << "[sets-prop]  ... via case 1b. ..." << std::endl;
    learnLiteral(right_literal, literal);
    if(d_conflict) return;

    // subsumption requirement met, exit
    return;
  }
  else if( holds(literal.negate() ) ) {
    // 4. neg(literal), left_literal => neg(right_literal)
    if( holds(left_literal) ) {
      Debug("sets-prop") << "[sets-prop]  ... via case 4. ..." << std::endl;
      learnLiteral(right_literal.negate(), AND( literal.negate(), 
                                                left_literal) );
      if(d_conflict) return;
    }

    // 5. neg(literal), right_literal => neg(left_literal)
    if( holds(right_literal) ) {
      Debug("sets-prop") << "[sets-prop]  ... via case 5. ..." << std::endl;
      learnLiteral(left_literal.negate(), AND( literal.negate(),
                                               right_literal) );
      if(d_conflict) return;
    }
  }
  else {
    // 2,3. neg(left_literal) v neg(right_literal) => neg(literal)
    if(holds(left_literal.negate())) {
      Debug("sets-prop") << "[sets-prop]  ... via case 2. ..." << std::endl;
      learnLiteral(literal.negate(), left_literal.negate());
      if(d_conflict) return;
    }
    else if(holds(right_literal.negate())) {
      Debug("sets-prop") << "[sets-prop]  ... via case 3. ..." << std::endl;
      learnLiteral(literal.negate(), right_literal.negate());
      if(d_conflict) return;
    }

    // 6. the axiom itself:
    else if(holds(left_literal) && holds(right_literal)) {
      Debug("sets-prop") << "[sets-prop]  ... via case 6. ..." << std::endl;
      learnLiteral(literal, AND(left_literal, right_literal) );
      if(d_conflict) return;
    }
  }

  // checkFulfillingRule
  Node n;
  switch(S.getKind()) {
  case kind::UNION:
    if( holds(IN(x, S)) &&  
        !present( IN(x, S[0]) ) )
      addToPending( IN(x, S[0]) );
    break;
  case kind::SETMINUS: // intentional fallthrough
  case kind::INTERSECTION:
    if( holds(IN(x, S[0])) &&
        !present( IN(x, S[1]) ))
      addToPending( IN(x, S[1]) );
    break;
  default:
    Assert(false, "MembershipEngine::doSettermPropagation");
  }
}

void TheorySetsPrivate::registerReason(TNode reason, bool save)
{
  if(save) d_nodeSaver.insert(reason);

  if(reason.getKind() == kind::AND) {
    Assert(reason.getNumChildren() == 2);
    registerReason(reason[0], false);
    registerReason(reason[1], false);
  } else if(reason.getKind() == kind::NOT) {
    registerReason(reason[0], false);
  } else if(reason.getKind() == kind::IN) {
    d_equalityEngine.addTriggerPredicate(reason);
    Assert(present(reason));
  } else if(reason.getKind() == kind::EQUAL) {
    d_equalityEngine.addTriggerEquality(reason);
  } else {
    Unhandled();
  }
}


void TheorySetsPrivate::learnLiteral(TNode atom, bool polarity, Node reason) {
  Debug("sets-learn") << "[sets-learn] learnLiteral(" << atom
                      << ", " << polarity << ")" << std::endl;

  if( holds(atom, polarity) ) {
    Debug("sets-learn") << "[sets-learn] \u2514 already known, skipping" << std::endl;
    return;
  }

  if( holds(atom, !polarity) ) {
    Debug("sets-learn") << "[sets-learn] \u2514 conflict found" << std::endl;
    
    registerReason(reason, /*save=*/ true);

    if(atom.getKind() == kind::EQUAL) {
      d_equalityEngine.assertEquality(atom, polarity, reason);
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, reason);
    }
    Assert(d_conflict);       // should be marked due to equality engine
    return;
  }

  Assert(atom.getKind() == kind::EQUAL || atom.getKind() == kind::IN);

  Node learnt_literal = polarity ? Node(atom) : NOT(atom);
  d_propagationQueue.push_back( make_pair(learnt_literal, reason) );
}

void TheorySetsPrivate::finishPropagation()
{
  while(!d_conflict && !d_propagationQueue.empty()) {
    std::pair<Node,Node> np = d_propagationQueue.front();
    d_propagationQueue.pop();
    TNode atom = np.first.getKind() == kind::NOT ? np.first[0] : np.first;
    if(atom.getKind() == kind::IN) {
      assertMemebership(np.first, np.second, /* learnt = */ true);
    } else {
      assertEquality(np.first, np.second, /* learnt = */ true);
    }
  }
}

void TheorySetsPrivate::addToPending(Node n) {
  if(d_pendingEverInserted.find(n) == d_pendingEverInserted.end()) {
    if(n.getKind() == kind::IN) {
      d_pending.push(n);
    } else {
      Assert(n.getKind() == kind::EQUAL);
      d_pendingDisequal.push(n);
    }
    d_pendingEverInserted.insert(n);
  }
}

bool TheorySetsPrivate::isComplete() {
  while(!d_pending.empty() && present(d_pending.front()))
    d_pending.pop();
  return d_pending.empty() && d_pendingDisequal.empty();
}


Node TheorySetsPrivate::getLemma() {
  Assert(!d_pending.empty() || !d_pendingDisequal.empty());

  Node lemma;

  if(!d_pending.empty()) {
    Node n = d_pending.front();
    d_pending.pop();

    Assert(!present(n));
    Assert(n.getKind() == kind::IN);

    lemma = OR(n, NOT(n));
  } else {
    Node n = d_pendingDisequal.front();
    d_pendingDisequal.pop();

    Assert(n.getKind() == kind::EQUAL && n[0].getType().isSet());
    Node x = NodeManager::currentNM()->mkSkolem("sde_$$", n[0].getType().getSetElementType());
    Node l1 = IN(x, n[0]), l2 = IN(x, n[1]);

    // d_equalityEngine.addTerm(x);
    // d_equalityEngine.addTerm(l1);
    // d_equalityEngine.addTerm(l2);
    // d_terms.insert(x);

    lemma = OR(AND(l1, NOT(l2)), AND(NOT(l1), l2)); 
  }

  Debug("sets-lemma") << "[sets-lemma] " << lemma << std::endl;

  return  lemma;
}


TheorySetsPrivate::TheorySetsPrivate(TheorySets& external,
                                     context::Context* c,
                                     context::UserContext* u,
                                     OutputChannel& out,
                                     Valuation valuation,
                                     const LogicInfo& logicInfo,
                                     QuantifiersEngine* qe) :
  d_external(external),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sets::TheorySetsPrivate"),
  d_conflict(c),
  d_termInfoManager(NULL),
  d_propagationQueue(c),
  d_nodeSaver(c),
  d_complete(c),
  d_pending(c),
  d_pendingDisequal(c),
  d_pendingEverInserted(c)
{
  d_termInfoManager = new TheorySetsTermInfoManager(c, &d_equalityEngine);

  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);

  d_equalityEngine.addFunctionKind(kind::IN);
  d_equalityEngine.addFunctionKind(kind::SUBSET);
}/* TheorySetsPrivate::TheorySetsPrivate() */

TheorySetsPrivate::~TheorySetsPrivate()
{
  delete d_termInfoManager;
}

void TheorySetsPrivate::check(Theory::Effort level) {

  while(!d_external.done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = d_external.get();
    TNode fact = assertion.assertion;

    Debug("sets") << "\n\n[sets] TheorySetsPrivate::check(): processing "
                  << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    // Solve each
    switch(atom.getKind()) {
    case kind::EQUAL:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be equal to " << atom[1] << std::endl;
      assertEquality(fact, fact, /* learnt = */ false);
      break;

    case kind::IN:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be in " << atom[1] << std::endl;
      assertMemebership(fact, fact, /* learnt = */ false);
      break;

    default:
      Unhandled(fact.getKind());
    }
    finishPropagation();

    Debug("sets") << "[sets]"
                  << "  in conflict = " << d_conflict
                  << ", is complete = " << isComplete()
                  << std::endl;

    if(d_conflict && !d_equalityEngine.consistent()) continue;
    Assert(!d_conflict);
    Assert(d_equalityEngine.consistent());
  }

  if(!isComplete()) {
    d_external.d_out->lemma(getLemma());
  }

  return;
}/* TheorySetsPrivate::check() */

void TheorySetsPrivate::conflict(TNode a, TNode b)
{
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain(a.iffNode(b));
  } else {
    d_conflictNode = explain(a.eqNode(b));
  }
  d_external.d_out->conflict(d_conflictNode);
  Debug("sets") << "[sets] conflict: " << a << " iff " << b
                << ", explaination " << d_conflictNode << std::endl;
  d_conflict = true;
}

Node TheorySetsPrivate::explain(TNode literal)
{
  Debug("sets") << "TheorySetsPrivate::explain(" << literal << ")"
                << std::endl;

  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> assumptions;
  if(!d_equalityEngine.consistent() && (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) ) {
     d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else if(!d_equalityEngine.consistent() && atom.getKind() == kind::IN) {
    if(d_equalityEngine.hasTerm(atom) == false) {
      d_equalityEngine.addTriggerPredicate(atom);
    }
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  } else {
    Debug("sets") << "unhandled: " << literal << "; (" << atom << ", " << polarity << "); kind" << atom.getKind() << std::endl;
    Unhandled();
  }
  return mkAnd(assumptions);
}

void TheorySetsPrivate::preRegisterTerm(TNode node)
{
  Debug("sets") << "TheorySetsPrivate::preRegisterTerm(" << node << ")"
                << std::endl;

  switch(node.getKind()) {
  case kind::EQUAL:
    // TODO: what's the point of this
    d_equalityEngine.addTriggerEquality(node);
    break;
  case kind::IN:
    // TODO: what's the point of this
    d_equalityEngine.addTriggerPredicate(node);
    break;
  default:
    d_termInfoManager->addTerm(node);
    d_equalityEngine.addTriggerTerm(node, THEORY_SETS);
    d_equalityEngine.addTerm(node);
  }

}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerEquality: equality = " << equality << " value = " << value << std::endl;
  // d_membershipEngine->eqNotifyEqual(equality, value);
  return true;
}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerPredicate: predicate = " << predicate << " value = " << value << std::endl;
  return true;
}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerTermEquality: tag = " << tag << " t1 = " << t1 << "  t2 = " << t2 << "  value = " << value << std::endl;
  d_theory.d_termInfoManager->mergeTerms(t1, t2);
  return true;
}

void TheorySetsPrivate::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyConstantTermMerge " << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}
void TheorySetsPrivate::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyNewClass:" << " t = " << t << std::endl;
}

void TheorySetsPrivate::NotifyClass::eqNotifyPreMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPreMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
}

void TheorySetsPrivate::NotifyClass::eqNotifyPostMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
}

void TheorySetsPrivate::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyDisequal:" << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason << std::endl;
}


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
