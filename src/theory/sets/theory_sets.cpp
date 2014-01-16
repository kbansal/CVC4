#include "theory/sets/theory_sets.h"
#include "theory/sets/theory_sets_private.h"

namespace CVC4 {
namespace theory {
namespace sets {

TheorySets::TheorySets(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       QuantifiersEngine* qe) :
  Theory(THEORY_SETS, c, u, out, valuation, logicInfo, qe),
  d_internal(new TheorySetsPrivate(*this, c,u,out,valuation,logicInfo,qe)) {
}

TheorySets::~TheorySets() { delete d_internal; }

void
TheorySets::check(Effort e)
{ d_internal->check(e);}

Node
TheorySets::explain(TNode node)
{ return d_internal->explain(node); }
  
void
TheorySets::preRegisterTerm(TNode node)
{ return d_internal->preRegisterTerm(node); }

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
