#include "expr/attribute.h"

namespace CVC4 {
namespace theory {
namespace attr {
  struct DecisionWeightTag {};
}/* CVC4::theory::attr namespace */

typedef expr::Attribute<attr::DecisionWeightTag, uint64_t> DecisionWeightAttr;

}/* CVC4::theory namespace */
}/* CVC4 namespace */
