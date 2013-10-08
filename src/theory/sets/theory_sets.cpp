#include "theory/sets/theory_sets.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace sets {

/** Constructs a new instance of TheorySets w.r.t. the provided contexts. */
TheorySets::TheorySets(context::Context* c,
                           context::UserContext* u,
                           OutputChannel& out,
                           Valuation valuation,
                           const LogicInfo& logicInfo,
                           QuantifiersEngine* qe) :
  Theory(THEORY_SETS, c, u, out, valuation, logicInfo, qe) {
}/* TheorySets::TheorySets() */

void TheorySets::check(Effort level) {
  while(!done()) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("sets") << "TheorySets::check(): processing " << fact << std::endl;

    continue;
    // Do the work
    switch(fact.getKind()) {

    /* cases for all the theory's kinds go here... */

    default:
      Unhandled(fact.getKind());
    }
  }

}/* TheorySets::check() */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
