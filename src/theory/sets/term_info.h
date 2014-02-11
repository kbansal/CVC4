
namespace CVC4 {
namespace theory {
namespace sets {


typedef context::CDList<TNode> CDTNodeList;
typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;
typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;

class TheorySetsTermInfo {
  TNode d_term;                 // actually unnecessary since we
                                // maintain the invariant that
                                // inThisEqClass' first element will
                                // be d_term
public:

  CDTNodeList* elementsInThisSet;
  CDTNodeList* elementsNotInThisSet;
  CDTNodeList* parents;

  TheorySetsTermInfo(TNode t, context::Context* c):
    d_term(t)
  {
    Debug("sets-terminfo") << "[sets-terminfo] Creating info for " << d_term
                           << std::endl;

    elementsInThisSet = new(true)CDTNodeList(c);
    elementsNotInThisSet = new(true)CDTNodeList(c);
    parents = new(true)CDTNodeList(c);
  }

  void addToElementList(TNode n, bool polarity) {
    if(polarity) elementsInThisSet -> push_back(n);
    else elementsNotInThisSet -> push_back(n);
  }

  ~TheorySetsTermInfo() {
    Debug("sets-terminfo") << "[sets-terminfo] Destroying info for " << d_term
                           << std::endl;

    elementsInThisSet -> deleteSelf();
    elementsNotInThisSet -> deleteSelf();
    parents -> deleteSelf();
  }
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
