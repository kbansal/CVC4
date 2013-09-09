#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H
#define __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace sets {

class SetsTypeRule {
public:

  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of sets.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check)
    throw (TypeCheckingExceptionPrivate) {

    // TODO: implement me!
    Unimplemented();

  }

};/* class SetsTypeRule */

struct SetsProperties {
  inline static Cardinality computeCardinality(TypeNode type) {
    Assert(type.getKind() == kind::SET_TYPE);
    Cardinality elementCard = type[0].getCardinality();
    return elementCard;
  }
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_TYPE_RULES_H */
