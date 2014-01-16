#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H
#define __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H

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
  TheorySets& d_theorySetsExternal;

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
};/* class TheorySetsPrivate */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
