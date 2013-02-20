#ifndef __CVC4__THEORY__DECISION_ATRRIBUTES
#define __CVC4__THEORY__DECISION_ATRRIBUTES

#include "expr/attribute.h"

namespace CVC4 {
namespace decision {
typedef uint64_t DecisionWeight;
}
namespace theory {
namespace attr {
  struct DecisionWeightTag {};
}/* CVC4::theory::attr namespace */

typedef expr::Attribute<attr::DecisionWeightTag, decision::DecisionWeight> DecisionWeightAttr;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DECISION_ATRRIBUTES */
