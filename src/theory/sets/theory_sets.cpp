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

class Pattern {
protected:
  bool d_matched;
  TNode d_match;
public:
  virtual bool test(TNode n) { return true; }
  virtual ~Pattern() {}
  bool match(TNode n) {
    d_matched = test(n);
    if(d_matched) d_match = n;
    return d_matched;
  }
  virtual Node build() { Assert(d_matched); return d_match; }
};

class SetTerm : public Pattern {
public:
  virtual ~SetTerm() {}
  virtual bool test(TNode n) { return kindToTheoryId(n.getKind()) == theory::THEORY_SETS;  }
};

class IN : public Pattern {
  Pattern& d_ele, &d_set;
public:
  IN(Pattern& ele, Pattern& set):d_ele(ele), d_set(set) {}
  bool test(TNode n) {
    return n.getKind() == kind::IN && d_ele.match(n[0]) && d_set.match(n[1]);
  }
  Node build() {
    NodeManager *nm = NodeManager::currentNM();
    return nm->mkNode(kind::IN, d_ele.build(), d_set.build());
  }
};

class INTERSECTION : public Pattern {
  Pattern& d_seta, &d_setb;
public:
  INTERSECTION(Pattern& seta, Pattern& setb):d_seta(seta), d_setb(setb) {}
  bool test(TNode n) {
    return n.getKind() == kind::INTERSECTION && d_seta.match(n[0]) && d_setb.match(n[1]);
  }
  Node build() {
    NodeManager *nm = NodeManager::currentNM();
    return nm->mkNode(kind::INTERSECTION, d_seta.build(), d_setb.build());
  }
};
class UNION : public Pattern {
  Pattern& d_seta, &d_setb;
public:
  UNION(Pattern& seta, Pattern& setb):d_seta(seta), d_setb(setb) {}
  bool test(TNode n) {
    return n.getKind() == kind::UNION && d_seta.match(n[0]) && d_setb.match(n[1]);
  }
  Node build() {
    NodeManager *nm = NodeManager::currentNM();
    return nm->mkNode(kind::UNION, d_seta.build(), d_setb.build());
  }
};

class SetsHelper {

  TNodeSet d_allConstraints;

  bool propagate(TNode n) {
    if(d_allConstraints.find(n) == d_allConstraints.end()) {
      return false;
    }

    // not found, insert
    d_allConstraints.insert(n);
    return true;
  }
public:
  bool applySaturationRule(TNode n, Constraints constraints) {
    // The term must have a valuation
    Pattern e;
    Pattern s1, s2;
    INTERSECTION inter(s1, s2);
    IN rule1(e, inter);
    IN rule1impA(e, s1), rule1impB(e, s2);

    if( rule1.match(n)) {
      Debug("pattern") << "rule1 match: " << n << endl;
      // propagate(
    } else {
      Debug("pattern") << "NO match " << n << endl;
    }

    for(unsigned i = 0; i < n.getNumChildren(); ++i) {
      applySaturationRule(n[i], constraints);
    }
    // SatValue v = getValuation(n);
    // if(n.getKind() == kind::IN && v == SAT_VALUE_TRUE &&
    //    n[1].getKind() == kind::INTERSECTION && ) {
    //   if( IN(... , ) );
    // }
    return false;
  }

  Result::Sat check(Constraints c) {
    // What's the idea?

    map<TNode, Result::Sat, TNodeHashFunction> valuation;

    TNodeSet terms;

    // Saturate c, generating new constraints which we call extra_c
    Constraints extra_c;
    
    for(typeof(c.equalities.begin()) i = c.equalities.begin(); i != c.equalities.end(); ++i)  
      applySaturationRule(*i, c);

    /**
     * What goes on in saturate?
     * Use one of the rules, do get a new propagation:
     *    if it already exists, we say voila -- that's it! stop search.
     *    what if it isn't -- add the propagation, and store the source (extra_c)
     */

    /**
     * If terminates with UNSAT,
     * To get an explanation, just trace back to the roots of the
     * conflicting literal. Done!
     */

    /**
     * If terminates with SAT, need to use one of the fulfilling rules
     * Do that. Send to SAT solver forget about it.
     * If all subsumption requirements met, done. Exit with SAT.
     */

    /**
     * What data structures to keep?
     *   actual assertions, and our propagations
     */
    return Result::SAT;
  }
};/* SetsHelper */


/** Constructs a new instance of TheorySets w.r.t. the provided contexts. */
TheorySets::TheorySets(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       QuantifiersEngine* qe) :
  Theory(THEORY_SETS, c, u, out, valuation, logicInfo, qe),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sets::TheorySets"),
  d_conflict(c) {

  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);

  d_equalityEngine.addFunctionKind(kind::IN);
}/* TheorySets::TheorySets() */


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
      if(!polarity)
        nonmemberships.insert(atom);
      else
        memberships.insert(atom);
      break;
    default:
      Unhandled(fact.getKind());
    }

    // Run check
    SetsHelper setsHelper;
    Result::Sat result;
    Constraints c; c.equalities = memberships;
    result = setsHelper.check(c);

    // Possiblities: conflict, sat, or need to assert something
    if(result == Result::SAT) {
    } else if(result == Result::UNSAT) {
      //setsHelper.getExplanation();
    } else if(result == Result::SAT_UNKNOWN) {
      //d_out->lemma(setsHelper.getLemma());
    } else {
      Unhandled();
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

void TheorySets::PreRegisterTerm(TNode n)
{
  // switch(n.getKind()) {
  // // case kind::EQUAL:
  // //   d_equalityEngine.addTriggerEquality(n);
  // //   break;
  // // case kind::IN:
  // //   d_equalityEngine.addTriggerPredicate(n);
  // //   break;
  // default:
  //   // Assert(n.getType().isSet());
  //   d_equalityEngine.addTerm(n);
  // }
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
