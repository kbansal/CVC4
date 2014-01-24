#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H
#define __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H

#include "context/cdhashset.h"
#include "context/cdqueue.h"

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

/** Internal classes, forward declared here */
class TheorySetsTermInfoManager;
class TheorySets;

class TheorySetsPrivate {
public:

  /**
   * Constructs a new instance of TheorySetsPrivate w.r.t. the provided
   * contexts.
   */
  TheorySetsPrivate(TheorySets& external,
                    context::Context* c,
                    context::UserContext* u,
                    OutputChannel& out,
                    Valuation valuation,
                    const LogicInfo& logicInfo,
                    QuantifiersEngine* qe);

  ~TheorySetsPrivate();

  void check(Theory::Effort);

  Node explain(TNode);
  
  std::string identify() const { return "THEORY_SETS_PRIVATE"; }

  void preRegisterTerm(TNode node);

private:
  TheorySets& d_external;

  /** Functions to handle callbacks from equality engine */
  class NotifyClass : public eq::EqualityEngineNotify {
    TheorySetsPrivate& d_theory;

  public:
    NotifyClass(TheorySetsPrivate& theory): d_theory(theory) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value);
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value);
    void eqNotifyConstantTermMerge(TNode t1, TNode t2);
    void eqNotifyNewClass(TNode t);
    void eqNotifyPreMerge(TNode t1, TNode t2);
    void eqNotifyPostMerge(TNode t1, TNode t2);
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  } d_notify;

  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;

  context::CDO<bool> d_conflict;
  Node d_conflictNode;

  void conflict(TNode, TNode);

  TheorySetsTermInfoManager* d_termInfoManager;

  struct AtomInfo {
    bool polarity;
    bool learnt;
  };

  /** Assertions and helper functions */
  bool present(TNode atom);
  bool holds(TNode lit) {
    bool polarity = lit.getKind() == kind::NOT ? false : true;
    TNode atom = polarity ? lit : lit[0];
    return holds(atom, polarity);
  }
  bool holds(TNode atom, bool polarity);

  void assertEquality(TNode fact, TNode reason, bool learnt);
  void assertMemebership(TNode fact, TNode reason, bool learnt);

  /** Propagation / learning and helper functions. */

  context::CDQueue< std::pair<Node, Node> > d_propagationQueue;

  void doSettermPropagation(TNode x, TNode S);
  void registerReason(TNode reason, bool save);
  void learnLiteral(TNode atom, bool polarity, Node reason);
  void learnLiteral(TNode lit, Node reason) {
    if(lit.getKind() == kind::NOT) {
      learnLiteral(lit[0], false, reason);
    } else {
      learnLiteral(lit, true, reason);
    }
  }
  void finishPropagation();

  // for any nodes we need to save, because others use TNode
  context::CDHashSet <Node, NodeHashFunction> d_nodeSaver;

  /** Lemmas and helper functions */
  context::CDO<bool> d_complete;
  context::CDQueue <TNode> d_pending;
  context::CDQueue <TNode> d_pendingDisequal;
  context::CDHashSet <Node, NodeHashFunction> d_pendingEverInserted;

  void addToPending(Node n);
  bool isComplete();
  Node getLemma();

};/* class TheorySetsPrivate */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
