// only included in exactly one file so far
// but TODO: appropriate headers etc

namespace CVC4 {
namespace expr {
namespace pattern {

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
