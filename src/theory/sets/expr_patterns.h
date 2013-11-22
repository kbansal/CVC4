// only included in exactly one file so far
// but TODO: appropriate headers etc

namespace CVC4 {
namespace expr {
namespace pattern {

Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */

static Node AND(TNode a, TNode b) {
  NodeBuilder< > nb(kind::AND);
  nb << a << b ;
  return nb.constructNode();
}

static Node OR(TNode a, TNode b) {
  NodeBuilder< > nb(kind::OR);
  nb << a << b ;
  return nb.constructNode();
}

static Node IN(TNode a, TNode b) {
  NodeBuilder< > nb(kind::IN);
  nb << a << b ;
  return nb.constructNode();
}

static Node EQUAL(TNode a, TNode b) {
  NodeBuilder< > nb(kind::EQUAL);
  nb << a << b ;
  return nb.constructNode();
}

static Node NOT(TNode a) {
  return a.notNode();
}

}
}
}
