#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_H
#define __CVC4__THEORY__SETS__THEORY_SETS_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySets : public Theory {
public:

  /** Constructs a new instance of TheorySets w.r.t. the provided contexts. */
  TheorySets(context::Context* c,
               context::UserContext* u,
               OutputChannel& out,
               Valuation valuation,
               const LogicInfo& logicInfo,
               QuantifiersEngine* qe);

  void check(Effort);

  std::string identify() const {
    return "THEORY_SETS";
  }

};/* class TheorySets */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_H */
