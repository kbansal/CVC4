#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_H
#define __CVC4__THEORY__SETS__THEORY_SETS_H

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

class MembershipEngine;

class TheorySets : public Theory {
public:

  /**
   * Constructs a new instance of TheorySets w.r.t. the provided
   * contexts.
   */
  TheorySets(context::Context* c,
               context::UserContext* u,
               OutputChannel& out,
               Valuation valuation,
               const LogicInfo& logicInfo,
               QuantifiersEngine* qe);

  ~TheorySets();

  void check(Effort);

  Node explain(TNode);
  
  std::string identify() const { return "THEORY_SETS"; }

  void preRegisterTerm(TNode node);

private:

  /** Functions to handle callbacks from equality engine */
  class NotifyClass : public eq::EqualityEngineNotify {
    TheorySets& d_theory;

  public:
    NotifyClass(TheorySets& theory): d_theory(theory) {}
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

  MembershipEngine* d_membershipEngine;

  void conflict(TNode, TNode);
};/* class TheorySets */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_H */
