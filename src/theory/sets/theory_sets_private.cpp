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
  CDTNodeList* setsThisElementIsIn;
  CDTNodeList* parents;
  TheorySetsTermInfo(TNode t, context::Context* c):
    d_term(t)
  {
    Debug("sets-terminfo") << "[sets-terminfo] Creating info for " << d_term
                           << std::endl;

    inThisEqClass       = new(true)CDTNodeList(c);
    elementsInThisSet   = new(true)CDTNodeList(c);
    setsThisElementIsIn = new(true)CDTNodeList(c);
    parents             = new(true)CDTNodeList(c);

    inThisEqClass->push_back(t);
  }

  void addToSetList(TNode n)     { setsThisElementIsIn -> push_back(n); }
  void addToElementList(TNode n) { elementsInThisSet   -> push_back(n); }

  ~TheorySetsTermInfo() {
    Debug("sets-terminfo") << "[sets-terminfo] Destroying info for " << d_term
                           << std::endl;

    inThisEqClass       -> deleteSelf();
    elementsInThisSet   -> deleteSelf();
    setsThisElementIsIn -> deleteSelf();
    parents             -> deleteSelf();
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
    TNode x = atom[0], S = atom[1];

    Debug("sets-terminfo") << "[sets-terminfo] Adding membership " << x
                           << " in " << S << std::endl;


    x = d_eqEngine->getRepresentative(x);
    S = d_eqEngine->getRepresentative(S);

    d_info[x]->addToSetList(S);
    d_info[S]->addToElementList(x);
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

    for(unsigned i = 0; i < numChild; ++i)
      if(d_terms.contains(n[i]))
        d_info[n[i]]->parents->push_back(n);
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

    mergeLists((*ita).second->setsThisElementIsIn,
               (*itb).second->setsThisElementIsIn);
  }
         
};



/********************** Helper functions ***************************/
/********************** Helper functions ***************************/
/********************** Helper functions ***************************/

Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

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

void TheorySetsPrivate::assertEquality(TNode fact, TNode reason, bool learnt)
{
  Assert(learnt == false);
}

void TheorySetsPrivate::assertMemebership(TNode fact, TNode reason, bool learnt)
{
  Debug("sets-mem") << "\n[sets-mem] adding ( " << fact
                    << ", " << reason
                    << ", " << learnt << std::endl;

  // checkInvariants();

  bool polarity = fact.getKind() == kind::NOT ? false : true;
  TNode atom_tmp = polarity ? fact : fact[0];

  Assert(atom_tmp.getKind() == kind::IN);
  Node atom = IN( d_equalityEngine.getRepresentative(atom_tmp[0]),
                  d_equalityEngine.getRepresentative(atom_tmp[1]) );

  if(d_assertions.find(atom) != d_assertions.end() ) {
    if(d_assertions[atom].get().polarity != polarity) {

      if(!learnt) {
        Assert(d_assertions[atom].get().learnt,
               "Theory asserted both literal and negation?");
        AtomInfo new_info;
        new_info.polarity = polarity;
        new_info.learnt = learnt;
        d_assertions[atom] = new_info;
      }

      Debug("sets-mem") << "[sets-mem]  conflict found" << std::endl;
      d_conflict = true;
    }

    return;
  } else {
    Assert(atom.getNumChildren() == 2);
    AtomInfo atom_info;
    atom_info.polarity = polarity;
    atom_info.learnt = learnt;
    d_assertions[atom] = atom_info;
    d_termInfoManager->notifyMembership(atom); // atom -> fact perhpas

    if(polarity && atom[1].getKind() == kind::EMPTYSET) {
      Debug("sets-mem") << "[sets-mem]  something in empty set? conflict." << std::endl;
      d_conflict = true;
      return;
    }
  }

  //Propagation
  Debug("sets-prop") << "[sets-prop] Propagating 'down' " << std::endl;
  Debug("sets-prop") << "[sets-prop] Propagating 'eq' on element"
                     << d_equalityEngine.getRepresentative(atom[0]) << std::endl;
  for(eq::EqClassIterator i(d_equalityEngine.getRepresentative(atom[0]), 
                            &d_equalityEngine); !i.isFinished(); ++i) {

    for(eq::EqClassIterator j(d_equalityEngine.getRepresentative(atom[1]),
                              &d_equalityEngine); !j.isFinished(); ++j) {


      TNode x = (*i);
      TNode S = (*j);
      TNode cur_atom = IN(x, S);
      Node polarity_atom = NodeManager::currentNM()->mkConst<bool>(polarity);

      if(!d_equalityEngine.hasTerm(cur_atom) ||
         !d_equalityEngine.areEqual(cur_atom, polarity_atom) ) {
        Debug("sets-eq") << "[sets-eq] Should be propagating " << cur_atom 
                         << " with polarity = " << polarity << std::endl;
        d_equalityEngine.addTriggerPredicate(cur_atom);
      }

      if(S.getKind() == kind::UNION ||
         S.getKind() == kind::INTERSECTION ||
         S.getKind() == kind::SETMINUS || 
         S.getKind() == kind::SET_SINGLETON) {
        doSettermPropagation(x, S);
        if(d_conflict) return;
      }

      Debug("sets-prop") << "[sets-prop] Propagating 'up' for "
                         << x << element_of_str << S << std::endl;

      CDTNodeList* parentList = d_termInfoManager->getParents(S);
      for(typeof(parentList->begin()) k = parentList->begin();
          k != parentList->end(); ++k) {
        doSettermPropagation(x, *k);
        if(d_conflict) return;
      }

    }

  }

      // Debug("sets-prop-eq") << "[sets-prop-eq] " << fact << " : element : "
      //                       << d_equalityEngine.getRepresentative(atom[0]) << " "
      //                       << (*i) << std::endl;
      // if( (*i) == atom[0] ) continue; // does this ever happen?
      // learnLiteral(IN(*i, atom[1]), polarity);
      // if(d_conflict) return;

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

  // // checkFulfillingRule
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

void TheorySetsPrivate::learnLiteral(TNode atom, bool polarity, Node reason) {
  Debug("sets-learn") << "[sets-learn] learnLiteral(" << atom
                      << ", " << polarity << ")" << std::endl;
  if(d_assertions.find(atom) != d_assertions.end()) {
    if(d_assertions[atom].get().polarity != polarity) {
      Debug("sets-learn") << "conflict found" << std::endl;

      // TODO: following only for transition, get rid of it soon.

      // check same information is in the equality engine
      if(atom.getKind() == kind::IN) {
        TNode negpol_atom = NodeManager::currentNM()->mkConst<bool>(!polarity);
        Assert(d_equalityEngine.areEqual(atom, negpol_atom));
        d_nodeSaver.insert(reason);
        d_equalityEngine.assertPredicate(atom, polarity, reason);
      } else {
        Assert(atom.getKind() == kind::EQUAL);
        if(polarity)
          Assert(d_equalityEngine.areEqual(atom[0], atom[1]));
        else
          Assert(d_equalityEngine.areDisequal(atom[0], atom[1], false));
        d_equalityEngine.assertEquality(atom, polarity, reason);
      }

      Assert(d_conflict);       // should be marked due to equality engine
      d_conflict = true;
    }
  } else {
    Node learnt_literal = polarity ? Node(atom) : NOT(atom);
    if(d_conflict) return;
    if(atom.getKind() == kind::EQUAL) {
      Assert(false);
      d_nodeSaver.insert(reason);
      d_equalityEngine.assertEquality(atom, polarity, reason);
      if(!d_equalityEngine.consistent()) d_conflict = true;
    } else {
      d_nodeSaver.insert(reason);
      if(!d_equalityEngine.hasTerm(atom[0])) {
        d_equalityEngine.addTriggerTerm(atom[0], THEORY_SETS);
      }
      if(!d_equalityEngine.hasTerm(atom[1])) {
        d_equalityEngine.addTriggerTerm(atom[1], THEORY_SETS);
      }
      d_equalityEngine.assertPredicate(atom, polarity, reason);
      if(!d_equalityEngine.consistent()) d_conflict = true;
      assertMemebership(learnt_literal, learnt_literal, /* learnt = */ true);
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
  d_assertions(c),
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

    Debug("sets") << "\n\n[sets] TheorySetsPrivate::check(): processing " << fact
                  << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    // Send to EqualityEngine
    switch(atom.getKind()) {
    case kind::EQUAL:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be equal to " << atom[1] << std::endl;
      d_equalityEngine.assertEquality(atom, polarity, fact);
      break;

    case kind::IN:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be in " << atom[1] << std::endl;
      d_equalityEngine.assertPredicate(atom, polarity, fact);
      assertMemebership(fact, fact, /* learnt = */ false);
      break;

    default:
      Unhandled(fact.getKind());
    }
    if(d_conflict && !d_equalityEngine.consistent()) continue;

    // Handle membership predicates
    if(atom.getKind() == kind::IN) {

      Debug("sets") << "[sets]"
                    << "  in conflict = " << d_conflict
                    << ", is complete = " << isComplete()
                    << std::endl;

      if(d_conflict) {
        Node conflictNode = explain(fact);
        d_external.d_out->conflict(conflictNode);
      }
    }
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
  // d_conflictNode = explain(a.iffNode(b));
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
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
    // getCurrentAssertions(assumptions);
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
