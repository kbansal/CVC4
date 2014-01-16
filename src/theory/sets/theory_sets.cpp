#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "theory/sets/theory_sets.h"
#include "util/result.h"
#include "theory/sets/expr_patterns.h" // ONLY included here

using namespace std;
using namespace CVC4::expr::pattern;

namespace CVC4 {
namespace theory {
namespace sets {

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

class TheorySetsPrivate {

};

TheorySets::TheorySets(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       QuantifiersEngine* qe) :
  Theory(THEORY_SETS, c, u, out, valuation, logicInfo, qe),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sets::TheorySets"),
  d_conflict(c),
  d_termInfoManager(NULL) {

  d_termInfoManager = new TheorySetsTermInfoManager(c, &d_equalityEngine);

  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);

  d_equalityEngine.addFunctionKind(kind::IN);
  d_equalityEngine.addFunctionKind(kind::SUBSET);
}/* TheorySets::TheorySets() */

TheorySets::~TheorySets()
{
  delete d_termInfoManager;
}

void TheorySets::check(Effort level) {

  while(!done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("sets") << "\n\n[sets] TheorySets::check(): processing " << fact
                  << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    // Do the work
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
      d_termInfoManager->notifyMembership(fact);
      break;

    default:
      Unhandled(fact.getKind());
    }

    if(d_conflict) continue;

    // d_membershipEngine->assertFact(fact, fact, /* learnt = */ false);
    // Debug("sets") << "[sets]"
    //               << "  in conflict = " << d_membershipEngine->inConflict()
    //     	  << ", is complete = " << d_membershipEngine->isComplete()
    //               << std::endl;

    // if(d_membershipEngine->inConflict()) {
    //   Node conflictNode = explain(fact);
    //   d_out->conflict(conflictNode);
    // }

  }

  // if(!d_membershipEngine->isComplete()) {
  //   d_out->lemma(d_membershipEngine->getLemma());
  // }

  return;
}/* TheorySets::check() */

void TheorySets::conflict(TNode a, TNode b)
{
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain(a.iffNode(b));
  } else {
    d_conflictNode = explain(a.eqNode(b));
  }
  // d_conflictNode = explain(a.iffNode(b));
  d_out->conflict(d_conflictNode);
  Debug("sets") << "[sets] conflict: " << a << " iff " << b
                << ", explaination " << d_conflictNode << std::endl;
  d_conflict = true;
}

Node TheorySets::explain(TNode literal)
{
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> assumptions;
  if(!d_equalityEngine.consistent() && (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) ) {
     d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    Debug("sets") << "unhandled: " << literal << "; (" << atom << ", " << polarity << "); kind" << atom.getKind() << std::endl;
    Unhandled();
  }
  return mkAnd(assumptions);
}

void TheorySets::preRegisterTerm(TNode node)
{
  d_termInfoManager->addTerm(node);
  Debug("sets") << "TheorySets::preRegisterTerm(" << node << ")" << std::endl;
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
    d_equalityEngine.addTriggerTerm(node, THEORY_SETS);
    d_equalityEngine.addTerm(node);
  }
}

bool TheorySets::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerEquality: equality = " << equality << " value = " << value << std::endl;
  // d_membershipEngine->eqNotifyEqual(equality, value);
  return true;
}

bool TheorySets::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerPredicate: predicate = " << predicate << " value = " << value << std::endl;
  return true;
}

bool TheorySets::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerTermEquality: tag = " << tag << " t1 = " << t1 << "  t2 = " << t2 << "  value = " << value << std::endl;
  d_theory.d_termInfoManager->mergeTerms(t1, t2);
  return true;
}

void TheorySets::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyConstantTermMerge " << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}
void TheorySets::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyNewClass:" << " t = " << t << std::endl;
}

void TheorySets::NotifyClass::eqNotifyPreMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPreMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
}

void TheorySets::NotifyClass::eqNotifyPostMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
}

void TheorySets::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyDisequal:" << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason << std::endl;
}


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
