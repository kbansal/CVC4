#include "context/cdhashset.h"
#include "theory/sets/theory_sets.h"
#include "util/result.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace sets {

typedef hash_set<TNode,TNodeHashFunction> TNodeSet;

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

struct Constraints {
  TNodeSet equalities;
  TNodeSet disequalities;
  TNodeSet memberships;
  TNodeSet nonmemberships;
};

// class Pattern {
// protected:
//   bool d_matched;
//   TNode d_match;
// public:
//   Pattern() {}
//   Pattern(const TNode& n) { match(n); return; }
//   virtual bool test(TNode n) { return true; }
//   virtual ~Pattern() {}
//   bool match(TNode n) {
//     d_matched = test(n);
//     if(d_matched) d_match = n;
//     return d_matched;
//   }
//   virtual Node build() { Assert(d_matched); return d_match; }
// };

// class SetTerm : public Pattern {
// public:
//   virtual ~SetTerm() {}
//   virtual bool test(TNode n) { return kindToTheoryId(n.getKind()) == theory::THEORY_SETS;  }
// };

// class IN : public Pattern {
//   Pattern& d_ele, &d_set;
// public:
//   IN(Pattern& ele, Pattern& set):d_ele(ele), d_set(set) {}
//   bool test(TNode n) {
//     return n.getKind() == kind::IN && d_ele.match(n[0]) && d_set.match(n[1]);
//   }
//   Node build() {
//     NodeManager *nm = NodeManager::currentNM();
//     return nm->mkNode(kind::IN, d_ele.build(), d_set.build());
//   }
// };

// class INTERSECTION : public Pattern {
//   Pattern& d_seta, &d_setb;
// public:
//   INTERSECTION(Pattern& seta, Pattern& setb):d_seta(seta), d_setb(setb) {}
//   bool test(TNode n) {
//     return n.getKind() == kind::INTERSECTION && d_seta.match(n[0]) && d_setb.match(n[1]);
//   }
//   Node build() {
//     NodeManager *nm = NodeManager::currentNM();
//     return nm->mkNode(kind::INTERSECTION, d_seta.build(), d_setb.build());
//   }
// };

// class UNION : public Pattern {
//   Pattern& d_seta, &d_setb;
// public:
//   UNION(Pattern& seta, Pattern& setb):d_seta(seta), d_setb(setb) {}
//   bool test(TNode n) {
//     return n.getKind() == kind::UNION && d_seta.match(n[0]) && d_setb.match(n[1]);
//   }
//   Node build() {
//     NodeManager *nm = NodeManager::currentNM();
//     return nm->mkNode(kind::UNION, d_seta.build(), d_setb.build());
//   }
// };

// class EQUAL : public Pattern {
//   Pattern& d_a, &d_b;
// public:
//   EQUAL(Pattern& a, Pattern& b):d_a(a), d_b(b) {}
//   bool test(TNode n) {
//     return n.getKind() == kind::EQUAL && d_a.match(n[0]) && d_b.match(n[1]);
//   }
//   Node build() {
//     NodeManager *nm = NodeManager::currentNM();
//     return nm->mkNode(kind::EQUAL, d_a.build(), d_b.build());
//   }
// };

// static Node EQUAL(TNode a, TNode b) {
//   NodeBuilder<kind::EQUAL> nb;
//   nb << a << b ;
//   return nb.constructNode();
// }
static Node IN(TNode a, TNode b) {
  NodeBuilder< > nb(kind::IN);
  nb << a << b ;
  return nb.constructNode();
}

static Node NOT(TNode a) {
  return a.notNode();
}

class MembershipEngine {
private:
  context::Context *d_context;

  typedef context::CDHashSet<Node, NodeHashFunction> CDSetNode;
  CDSetNode d_terms;

  typedef context::CDHashSet<Node, NodeHashFunction> Collection; // set of sets/elements
  typedef hash_map <TNode, Collection*, TNodeHashFunction> TNodeToCollectionMap;

  // mem[a] = {

  struct Info {
    bool polarity;
  };

  // context::CDHashMap <TNode, Info, TNodeHashFunction> d_assertions;

  struct State {
    TNodeToCollectionMap mem;    // all elements in TNode
    TNodeToCollectionMap notmem; // all elements not in TNode
    TNodeToCollectionMap in;     // all sets TNode is in
    TNodeToCollectionMap notin;  // all sets TNode is not in
  } d_state;

  queue<Node> d_assertionQueue;

  bool state_insert(TNodeToCollectionMap &m, TNode k, TNode v) {
    pair<TNodeToCollectionMap::iterator, bool> ret;
    if(m.find(k) == m.end()) {
      Collection *c = ::new Collection(d_context);
      m[k] = c;
    }
    return m[k]->insert(v);   // return if it was inserted
  }

  void state_reset(TNodeToCollectionMap &m) {
    TNodeToCollectionMap::iterator i;
    for(i=m.begin(); i != m.end(); ++i) {
      ::delete i->second;
    }
    m.clear();
  }

  bool state_contains(TNodeToCollectionMap &m, TNode k, TNode v) {
    if(m.find(k) == m.end()) return false;
    Assert(m[k] != NULL);
    return m[k]->find(v) != m[k]->end();
  }

  hash_map<TNode, set<TNode>, TNodeHashFunction> d_implications;
  void addImplication(TNode proposition, TNode consequence) {
    Debug("sets-mem-im") << "[sets-mem] saving implication " << proposition
                      << "  => " << consequence << std::endl;
    d_implications[proposition].insert(consequence);
  }

public:

  MembershipEngine(context::Context *c,
                   context::Context *u):
    d_context(c),
    d_terms(u) {
    ;
    // Pending propagations
    // Pending <atom --> subsumption requirements>
  }

  ~MembershipEngine() {
    // Delete all collections created
    state_reset(d_state.in);
    state_reset(d_state.notin);
    state_reset(d_state.mem);
    state_reset(d_state.notmem);
  }

  void addTerm(TNode x) {
    d_terms.insert(x);
  }

  void assertMembership(TNode x, TNode S, bool polarity, TNode reason) {
    Debug("sets-mem") << "[sets-mem] adding ( " << x
                      << ", " << S
                      << ", " << polarity
                      << ", " << reason << std::endl;
    // polarity( x in S )
    if(polarity) {
      Debug("sets-mem") << "[sets-mem]   adding to IN(" << x <<"):" << S << std::endl;
      bool ret = state_insert(d_state.in, x, S);
      if(ret == false) {        // Already exists, no further processing
        Assert(state_insert(d_state.mem, S, x) == false);
        return;
      }
      Debug("sets-mem") << "[sets-mem]   adding to MEM(" << S <<"):" << x << std::endl;
      state_insert(d_state.mem, S, x);
    } else {
      Debug("sets-mem") << "[sets-mem]   adding to NOT IN(" << x <<"):" << S << std::endl;
      bool ret = state_insert(d_state.notin, x, S);
      if(ret == false) {        // Already exists, no further processing 
        Assert(state_insert(d_state.notmem, S, x) == false);
      }
      Debug("sets-mem") << "[sets-mem]   adding to NOT MEM(" << S <<"):" << x << std::endl;
      state_insert(d_state.notmem, S, x);
    }

    switch(S.getKind()) {
    case kind::VARIABLE: {
      break;
    }
    case kind::UNION: {
      Debug("sets-mem") << "UNION: pending" << std::endl;
      if(polarity == false) {
        // x in S1 U S2 => x in S1, x in S2
        assertMembership(x, S[0], polarity, reason);
        assertMembership(x, S[1], polarity, reason);
      }
      if(polarity == true) {
        if( state_contains(d_state.notin, x, S[0]) ) {
          assertMembership(x, S[1], polarity, reason /*Incorrect*/);
          break;
        }
        if( state_contains(d_state.notin, x, S[1]) ) {
          assertMembership(x, S[0], polarity, reason /*Incorrect*/);
        }
        addImplication(NOT(IN(x, S[0])), IN(x, S));
        addImplication(NOT(IN(x, S[1])), IN(x, S));
      }
      break;
    }
    case kind::SET_SINGLETON: {
      assertEqual(x, S[0], polarity, reason);
      break;
    }
    default:
      Assert("Should had been one of the above kinds, what is wrong?");

    }
        
    // checkImplications(x, S, polarity);

  }

  void process() {
    // Step 1: when we get a new assertion, check all rules that might be relevant; add 
  }

  void assertEqual(TNode a, TNode b, bool polarity, TNode reason) {
    
  }
};

// class SetsHelper {

//   TNodeSet d_allConstraints;

//   bool propagate(TNode n) {
//     if(d_allConstraints.find(n) == d_allConstraints.end()) {
//       return false;
//     }

//     // not found, insert
//     d_allConstraints.insert(n);
//     return true;
//   }
// public:
//   bool applySaturationRule(TNode n, Constraints constraints) {
//     // The term must have a valuation
//     Pattern e;
//     Pattern s1, s2;
//     INTERSECTION inter(s1, s2);
//     IN rule1(e, inter);
//     IN rule1impA(e, s1), rule1impB(e, s2);

//     if( rule1.match(n)) {
//       Debug("pattern") << "rule1 match: " << n << endl;
//       // propagate(
//     } else {
//       Debug("pattern") << "NO match " << n << endl;
//     }

//     for(unsigned i = 0; i < n.getNumChildren(); ++i) {
//       applySaturationRule(n[i], constraints);
//     }
//     // SatValue v = getValuation(n);
//     // if(n.getKind() == kind::IN && v == SAT_VALUE_TRUE &&
//     //    n[1].getKind() == kind::INTERSECTION && ) {
//     //   if( IN(... , ) );
//     // }
//     return false;
//   }

//   Result::Sat check(Constraints c) {
//     // What's the idea?

//     map<TNode, Result::Sat, TNodeHashFunction> valuation;

//     TNodeSet terms;

//     // Saturate c, generating new constraints which we call extra_c
//     Constraints extra_c;
    
//     for(typeof(c.equalities.begin()) i = c.equalities.begin(); i != c.equalities.end(); ++i)  
//       applySaturationRule(*i, c);

//     /**
//      * What goes on in saturate?
//      * Use one of the rules, do get a new propagation:
//      *    if it already exists, we say voila -- that's it! stop search.
//      *    what if it isn't -- add the propagation, and store the source (extra_c)
//      */

//     /**
//      * If terminates with UNSAT,
//      * To get an explanation, just trace back to the roots of the
//      * conflicting literal. Done!
//      */

//     /**
//      * If terminates with SAT, need to use one of the fulfilling rules
//      * Do that. Send to SAT solver forget about it.
//      * If all subsumption requirements met, done. Exit with SAT.
//      */

//     /**
//      * What data structures to keep?
//      *   actual assertions, and our propagations
//      */
//     return Result::SAT;
//   }
// };/* SetsHelper */


TheorySets::TheorySets(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       QuantifiersEngine* qe) :
  Theory(THEORY_SETS, c, u, out, valuation, logicInfo, qe),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sets::TheorySets"),
  d_conflict(c),
  d_membershipEngine(new MembershipEngine(c, u)) {

  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);

  d_equalityEngine.addFunctionKind(kind::IN);
}/* TheorySets::TheorySets() */

TheorySets::~TheorySets()
{
  delete d_membershipEngine;
}

void TheorySets::check(Effort level) {

  // if(level != EFFORT_FULL) return;


  TNodeSet equalities;
  TNodeSet disequalities;
  TNodeSet memberships;
  TNodeSet nonmemberships;
  while(!done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("sets") << "TheorySets::check(): processing " << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    // Do the work
    switch(atom.getKind()) {

      /* cases for all the theory's kinds go here... */
    case kind::EQUAL:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be equal to " << atom[1] << std::endl;
      d_equalityEngine.assertEquality(atom, polarity, fact);
      if(!polarity)
        disequalities.insert(atom);
      else
        equalities.insert(atom);
      break;
    case kind::IN:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be in " << atom[1] << std::endl;
      d_equalityEngine.assertPredicate(atom, polarity, fact);
      d_membershipEngine->assertMembership(atom[0], atom[1], polarity, fact);
      if(!polarity)
        nonmemberships.insert(atom);
      else
        memberships.insert(atom);
      break;
    default:
      Unhandled(fact.getKind());
    }

  }
  return;
}/* TheorySets::check() */

void TheorySets::conflict(TNode a, TNode b)
{
  d_conflictNode = explain(a.iffNode(b));
  d_out->conflict(d_conflictNode);
  Debug("sets") << "[sets] conflict: " << a << " iff " << b
                << ", explaination " << d_conflictNode << std::endl;
  d_conflict = true;
}

Node TheorySets::explain(TNode literal)
{
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> assumptions;
  d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  return mkAnd(assumptions);
}

void TheorySets::preRegisterTerm(TNode n)
{
  switch(n.getKind()) {
  case kind::EQUAL:
    d_equalityEngine.addTriggerEquality(n);
    break;
  case kind::IN:
    // d_equalityEngine.addTriggerPredicate(n);
    break;
  default:
    // Assert(n.getType().isSet());
    d_equalityEngine.addTerm(n);
    d_membershipEngine->addTerm(n);
  }
}

bool TheorySets::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerEquality: equality = " << equality << " value = " << value << std::endl;
  return bool(); 
}
bool TheorySets::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerPredicate: predicate = " << predicate << " value = " << value << std::endl;
  return bool();
}
bool TheorySets::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerTermEquality: tag = " << tag << " t1 = " << t1 << "  t2 = " << t2 << "  value = " << value << std::endl;
  return bool();
}

void TheorySets::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyConstantTermMerge " << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}
void TheorySets::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyNewClass:" << " t = " << t << std::endl;
}
void TheorySets::NotifyClass::eqNotifyPreMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPreMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
}
void TheorySets::NotifyClass::eqNotifyPostMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
}
void TheorySets::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyDisequal:" << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason << std::endl;
}


//Data structures to keep:
// 1. Set of all terms
// 2. Current context

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
