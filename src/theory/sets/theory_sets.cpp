#include "context/cdhashset.h"
#include "context/cdqueue.h"
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

static Node NOT(TNode a) {
  return a.notNode();
}

// static Node INTERSECTION(TNode a, TNode b) {
//   NodeBuilder< > nb(kind::INTERSECTION);
//   nb << a << b ;
//   return nb.constructNode();
// }

class MembershipEngine {
private:
  context::Context *d_context;

  typedef context::CDHashSet<Node, NodeHashFunction> CDSetNode;
  CDSetNode d_terms;

  // TODO, Make this user context dependent
  std::hash_map<TNode, vector<TNode>, TNodeHashFunction> d_termParents;

  context::CDO<bool> d_conflict;
  context::CDO<bool> d_complete;

  typedef context::CDHashSet<Node, NodeHashFunction> Collection; // set of sets/elements
  typedef hash_map <TNode, Collection*, TNodeHashFunction> TNodeToCollectionMap;

  struct Info {
    bool polarity;
    bool learnt;
  };

  context::CDHashMap <Node, Info, NodeHashFunction> d_assertions;

  context::CDQueue <TNode> d_pending;
  context::CDHashSet <Node, NodeHashFunction> d_pendingEverInserted;

  Node d_lemma;

public:

  MembershipEngine(context::Context *c,
                   context::Context *u):
    d_context(c),
    d_terms(u),
    d_conflict(c),
    d_complete(c, true),
    d_assertions(c),
    d_pending(c),
    d_pendingEverInserted(c) {
    // Pending propagations
    // Pending <atom --> subsumption requirements>
  }

  ~MembershipEngine() {
  }

  bool inConflict() { return d_conflict; }

  void addTerm(TNode n) {
    if(n.getKind() == kind::EQUAL || n.getKind() == kind::IN) { 
      addTerm(n[0]);
    }
    else if(d_terms.find(n) == d_terms.end()){
      d_terms.insert(n);
      for(unsigned i = 0; i < n.getNumChildren(); ++i) {
        d_termParents[n[i]].push_back(n);
      }
    }
  }

  void printTermParents(TNode n) {
    for(unsigned i = 0; i < d_termParents[n].size(); ++i) {
      Debug("sets") << d_termParents[n][i];
    }
  }

  void printAllTermParents() {
    Debug("sets") << "[sets] printAllTermParents()\n";
    for(typeof(d_termParents.begin()) i = d_termParents.begin();
        i != d_termParents.end(); ++i) {
      Debug("sets") << "[sets]   parents of " << i->first << ": ";
      printTermParents(i->first);
      Debug("sets") << std::endl;
    }
  }

  void assertFact(TNode fact, TNode reason, bool learnt) {
    Debug("sets-mem") << "\n[sets-mem] adding ( " << fact
                      << ", " << reason
                      << ", " << learnt << std::endl;

    vector<TNode> v;
    getCurrentAssertions(v);

    bool polarity = fact.getKind() == kind::NOT ? false : true;
    TNode literal = polarity ? fact : fact[0];

    if(d_assertions.find(literal) != d_assertions.end()) {
      if(d_assertions[literal].get().polarity != polarity) {
        Assert("conflict found");
        d_conflict = true;
      }
      return;
      // Info& literal_info = d_assertions[fact];
    } else {
      Assert(literal.getNumChildren() == 2);
      Info literal_info;
      literal_info.polarity = polarity;
      literal_info.learnt = learnt;
      d_assertions[literal] = literal_info;
    }

    if(literal.getKind() != kind::EQUAL) {
      TNode x = literal[0];
      TNode S = literal[1];

      // propagate "down"
      if(S.getNumChildren() > 0) {
        doSettermPropagation(x, S);
        if(d_conflict) return;
      }

      // propagate "up"
      for(unsigned i = 0; i < d_termParents[S].size(); ++i) {
        doSettermPropagation(x, d_termParents[S][i]);
        if(d_conflict) return;
      }
    } else {
      // handleEqual(literal);
    }
    
    checkInvariants();
  }

  void doSettermPropagation(TNode x, TNode S) {
    Assert(S.getType().isSet() && S.getType().getSetElementType() == x.getType());

    Node literal, left_literal, right_literal;

    // axiom: literal <=> left_literal ^ right_literal
    switch(S.getKind()) {
    case kind::INTERSECTION:
      literal       =       IN(x, S)      ;
      left_literal  =       IN(x, S[0])   ; 
      right_literal =       IN(x, S[1])   ;
      break;
    case kind::UNION:
      literal       = NOT(  IN(x, S)     );
      left_literal  = NOT(  IN(x, S[0])  );
      right_literal = NOT(  IN(x, S[1])  );
      break;
    case kind::SETMINUS:
      literal       =       IN(x, S)      ;
      left_literal  =       IN(x, S[0])   ;
      right_literal = NOT(  IN(x, S[1])  );
      break;
    case kind::SET_SINGLETON:
      if(holds( IN(x, S) )) {
        assertEqual(x, S[0], true);
      } else {
        assertEqual(x, S[0], false);
      }
      break;
    default:
      Unhandled();
    }

    Assert( present( IN(x, S)    ) || 
	    present( IN(x, S[0]) ) || 
	    present( IN(x, S[1]) ) );

    if( holds(literal) ) {
      // 1a. literal => left_literal
      learnLiteral(left_literal);
      if(d_conflict) return;

      // 1b. literal => right_literal
      learnLiteral(right_literal);
      if(d_conflict) return;

      // subsumption requirement met, exit
      return;
    }
    else if( holds(literal.negate() ) ) {
      // 4. neg(literal), left_literal => neg(right_literal)
      if( holds(left_literal) ) {
        learnLiteral(right_literal.negate() );
        if(d_conflict) return;
      }

      // 5. neg(literal), right_literal => neg(left_literal)
      if( holds(right_literal) ) {
        learnLiteral(left_literal.negate() );
        if(d_conflict) return;
      }
    }
    else {
      // 2,3. neg(left_literal) v neg(right_literal) => neg(literal)
      if(holds(left_literal.negate()) || holds(right_literal.negate())) {
        learnLiteral(literal.negate());
        if(d_conflict) return;
      }

      // 6. the axiom itself:
      else if(holds(left_literal) && holds(right_literal)) {
        learnLiteral(literal);
        if(d_conflict) return;
      }
    }

    // checkFulfillingRule
    Node n;
    switch(S.getKind()) {
    case kind::UNION:
      if( holds(IN(x, S)) &&  
	  !present( IN(x, S[0]) ) )
	addToPending( IN(x, S[0]) );
      break;
    case kind::SETMINUS: // intentional fallthrough
    case kind::INTERSECTION:
      if( holds(IN(x, S[0])) &&
	  !present( IN(x, S[1]) ))
	addToPending( IN(x, S[1]) );
      break;
    default:
      Assert(false, "MembershipEngine::doSettermPropagation");
    }
  }

  bool checkInvariants() {
    // all assertions must contain terms which are in d_terms
    bool ret = true;
    for(typeof(d_assertions.begin()) i = d_assertions.begin();
        ret && i != d_assertions.end(); ++i) {
      TNode literal = (*i).first;
      Assert(literal.getKind() == kind::IN ||
             literal.getKind() == kind::EQUAL);
      ret = ret && d_terms.find(literal[0]) != d_terms.end()
        && d_terms.find(literal[1]) != d_terms.end();
      Assert(ret);         // can disable this later, if needed
    }
    return ret;
  }

  // returns true if something was added
  bool learnLiteral(TNode atom, bool polarity) {
    Debug("sets-learn") << "[sets-learn] learnLiteral(" << atom
                        << ", " << polarity << ")" << std::endl;
    if(d_assertions.find(atom) != d_assertions.end()) {
      if(d_assertions[atom].get().polarity != polarity) {
        Debug("sets-learn") << "conflict found" << std::endl;
        d_conflict = true;
      }
      return false;
    } else {
      Node learnt_literal = polarity ? Node(atom) : NOT(atom);
      assertFact(learnt_literal, learnt_literal, /* learnt = */ true);
      return true;
    }
  }

  bool learnLiteral(TNode lit) {
    return lit.getKind() == kind::NOT ?
      learnLiteral(lit[0], false) : learnLiteral(lit, true);
  }

  // A U B <=> A v B
  // A INT B <=> A ^ B
  // A \ B <=> A ^ (not B)

  bool applyRule1(TNode n, bool polarity) {
    bool added = false;
    if(polarity && n.getKind() == kind::IN 
       && n[1].getKind() == kind::INTERSECTION) {

      added = learnLiteral(IN(n[0], n[1][0]), polarity);
      if(d_conflict) return false;

      added |= learnLiteral(IN(n[0], n[1][1]), polarity);
      if(d_conflict) return false;
    }
    return added;
  }

  bool present(TNode n) {
    return d_assertions.find(n) != d_assertions.end();
  }

  bool holds(TNode lit) {
    bool polarity = lit.getKind() == kind::NOT ? false : true;
    TNode atom = polarity ? lit : lit[0];
    return present(atom) && d_assertions[atom].get().polarity == polarity;
  }

  bool checkSubsumption1(TNode n, bool polarity) {
    if(polarity && n.getKind() == kind::IN
       && n[1].getKind() == kind::UNION) {

      Node n1 = IN(n[0], n[1][0]);
      Node n2 = IN(n[0], n[1][1]);

      if(present(n1) && d_assertions[n1].get().polarity == polarity) {
        return true;
      }
      if(present(n2) && d_assertions[n2].get().polarity == polarity) {
        return true;
      }
      d_lemma = OR(n1, n2);
      return false;
    }
    return true;
  }

  void addToPending(Node n) {
    if(d_pendingEverInserted.find(n) == d_pendingEverInserted.end()) {
      d_pending.push(n);
      d_pendingEverInserted.insert(n);
    }
  }

  bool isComplete() {
    while(!d_pending.empty() && present(d_pending.front()))
      d_pending.pop();
    return d_pending.empty();
  }

  Node getLemma() {
    Assert(!d_pending.empty());
    Node n = d_pending.front();
    d_pending.pop();

    Assert(!present(n));
    Assert(n.getKind() == kind::IN);
    return OR(n, NOT(n));
  }

  // returns false if a conflict was found, true otherwise
  bool propagate() {
    static bool in_propagate = false;
    if(in_propagate) return true;
    in_propagate = true;
    // Step 1: when we get a new assertion, check all rules that might
    // be relevant
    bool anyChange = false;
    do {
      for(typeof(d_assertions.begin()) i = d_assertions.begin();
          i != d_assertions.end(); ++i) {
        anyChange = applyRule1( (*i).first, (*i).second.polarity);
        if(d_conflict) return false;
      }
    }while(anyChange);
    in_propagate = false;
    return true;
  }

  void getCurrentAssertions(std::vector<TNode>& assumptions) {
    Debug("sets-mem") << "[sets-mem] Current assertions:" << std::endl; 
    for(typeof(d_assertions.begin()) i = d_assertions.begin();
        i != d_assertions.end(); ++i) {
      if( (*i).second.learnt) continue;
      Node literal = (*i).second.polarity ? Node((*i).first) : NOT( (*i).first);
      assumptions.push_back(literal);
      Debug("sets-mem") << "[sets-mem]   " << literal << std::endl; 
    }
  }

  void assertEqual(TNode a, TNode b, bool polarity) {
    // What to do? Just go over all the assertions and replace any
    // occurence of "a" with b, and "b" with "a".

    // Also, add the equality to the a database. Thus, if anything
    // ever becomes equal, we'd propagate.
  }
};

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
  d_membershipEngine->printAllTermParents();

  TNodeSet equalities;
  TNodeSet disequalities;
  TNodeSet memberships;
  TNodeSet nonmemberships;
  while(!done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("sets") << "[sets] TheorySets::check(): processing " << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    // Do the work
    switch(atom.getKind()) {

      /* cases for all the theory's kinds go here... */
    case kind::EQUAL:
      // Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
      //               << "be equal to " << atom[1] << std::endl;
      d_equalityEngine.assertEquality(atom, polarity, fact);
      if(!polarity)
        disequalities.insert(atom);
      else
        equalities.insert(atom);
      break;
    case kind::IN:
      // Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
      //               << "be in " << atom[1] << std::endl;
      d_equalityEngine.assertPredicate(atom, polarity, fact);
      if(!polarity)
        nonmemberships.insert(atom);
      else
        memberships.insert(atom);
      break;
    default:
      Unhandled(fact.getKind());
    }
    if(d_conflict) continue;
    d_membershipEngine->assertFact(fact, fact, /* learnt = */ false);
    Debug("sets") << "[sets]  in conflict = " << d_membershipEngine->inConflict()
		  << ", is complete = " << d_membershipEngine->isComplete() << std::endl;
    if(d_membershipEngine->inConflict()) {
      Node conflictNode = explain(fact);
      d_out->conflict(conflictNode);
    }
  }
  if(!d_membershipEngine->isComplete()) {
    d_out->lemma(d_membershipEngine->getLemma());
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
  if(atom.getKind() == kind::EQUAL) {
     d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_membershipEngine->getCurrentAssertions(assumptions);
  }
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
