
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
  CDTNodeList* inThisEqClass;
  CDTNodeList* elementsInThisSet;
  CDTNodeList* elementsNotInThisSet;
  CDTNodeList* setsThisElementIsIn;
  CDTNodeList* setsThisElementIsNotIn;
  CDTNodeList* parents;
  TheorySetsTermInfo(TNode t, context::Context* c):
    d_term(t)
  {
    Debug("sets-terminfo") << "[sets-terminfo] Creating info for " << d_term
                           << std::endl;

    inThisEqClass = new(true)CDTNodeList(c);
    elementsInThisSet = new(true)CDTNodeList(c);
    elementsNotInThisSet = new(true)CDTNodeList(c);
    setsThisElementIsIn = new(true)CDTNodeList(c);
    setsThisElementIsNotIn = new(true)CDTNodeList(c);
    parents = new(true)CDTNodeList(c);

    inThisEqClass->push_back(t);
  }

  void addToSetList(TNode n, bool polarity) {
    if(polarity) setsThisElementIsIn -> push_back(n);
    else setsThisElementIsNotIn -> push_back(n);
  }
  void addToElementList(TNode n, bool polarity) {
    if(polarity) elementsInThisSet -> push_back(n);
    else elementsNotInThisSet -> push_back(n);
  }

  ~TheorySetsTermInfo() {
    Debug("sets-terminfo") << "[sets-terminfo] Destroying info for " << d_term
                           << std::endl;

    inThisEqClass -> deleteSelf();
    elementsInThisSet -> deleteSelf();
    elementsNotInThisSet -> deleteSelf();
    setsThisElementIsIn -> deleteSelf();
    setsThisElementIsNotIn -> deleteSelf();
    parents -> deleteSelf();
  }
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
