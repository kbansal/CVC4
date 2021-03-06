/*********************                                                        */
/*! \file theory_strings.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Martin Brain <>, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **
 ** Implementation of the theory of strings.
 **/


#include "theory/strings/theory_strings.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include "theory/rewriter.h"
#include "expr/command.h"
#include "theory/theory_model.h"
#include "smt/logic_exception.h"
#include "theory/strings/options.h"
#include "theory/strings/type_enumerator.h"
#include <cmath>

#define LAZY_ADD_MEMBERSHIP

using namespace std;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace strings {

Node TheoryStrings::TermIndex::add( Node n, unsigned index, TheoryStrings* t, Node er, std::vector< Node >& c ) {
  if( index==n.getNumChildren() ){
    if( d_data.isNull() ){
      d_data = n;
    }
    return d_data;
  }else{
    Assert( index<n.getNumChildren() );
    Node nir = t->getRepresentative( n[index] );
    //if it is empty, and doing CONCAT, ignore
    if( nir==er && n.getKind()==kind::STRING_CONCAT ){
      return add( n, index+1, t, er, c );
    }else{
      c.push_back( nir );
      return d_children[nir].add( n, index+1, t, er, c );
    }
  }
}


TheoryStrings::TheoryStrings(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo)
  : Theory(THEORY_STRINGS, c, u, out, valuation, logicInfo),
  RMAXINT(LONG_MAX),
  d_notify( *this ),
  d_equalityEngine(d_notify, c, "theory::strings::TheoryStrings", true),
  d_conflict(c, false),
  d_infer(c),
  d_infer_exp(c),
  d_nf_pairs(c),
  d_loop_antec(u),
  d_length_intro_vars(u),
  d_registered_terms_cache(u),
  d_preproc_cache(u),
  d_proxy_var(u),
  d_neg_ctn_eqlen(u),
  d_neg_ctn_ulen(u),
  d_pos_ctn_cached(u),
  d_neg_ctn_cached(u),
  d_ext_func_terms(c),
  d_regexp_memberships(c),
  d_regexp_ucached(u),
  d_regexp_ccached(c),
  d_pos_memberships(c),
  d_neg_memberships(c),
  d_inter_cache(c),
  d_inter_index(c),
  d_processed_memberships(c),
  d_regexp_ant(c),
  d_input_vars(u),
  d_input_var_lsum(u),
  d_cardinality_lits(u),
  d_curr_cardinality(c, 0)
{
  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::STRING_IN_REGEXP);
  d_equalityEngine.addFunctionKind(kind::STRING_LENGTH);
  d_equalityEngine.addFunctionKind(kind::STRING_CONCAT);
  d_equalityEngine.addFunctionKind(kind::STRING_STRCTN);
  d_equalityEngine.addFunctionKind(kind::STRING_SUBSTR_TOTAL);
  d_equalityEngine.addFunctionKind(kind::STRING_ITOS);
  d_equalityEngine.addFunctionKind(kind::STRING_STOI);
  if( options::stringLazyPreproc() ){
    d_equalityEngine.addFunctionKind(kind::STRING_U16TOS);
    d_equalityEngine.addFunctionKind(kind::STRING_STOU16);
    d_equalityEngine.addFunctionKind(kind::STRING_U32TOS);
    d_equalityEngine.addFunctionKind(kind::STRING_STOU32);
    d_equalityEngine.addFunctionKind(kind::STRING_STRIDOF);
    d_equalityEngine.addFunctionKind(kind::STRING_STRREPL);
  }

  d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
  d_emptyString = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
  std::vector< Node > nvec;
  d_emptyRegexp = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );

  d_card_size = 128;
  //d_opt_regexp_gcd = true;
}

TheoryStrings::~TheoryStrings() {

}

Node TheoryStrings::getRepresentative( Node t ) {
  if( d_equalityEngine.hasTerm( t ) ){
    return d_equalityEngine.getRepresentative( t );
  }else{
    return t;
  }
}

bool TheoryStrings::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheoryStrings::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryStrings::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  } else {
    if( a.getType().isString() ) {
      for( unsigned i=0; i<2; i++ ) {
        Node ac = a.getKind()==kind::STRING_CONCAT ? a[i==0 ? 0 : a.getNumChildren()-1] : a;
        Node bc = b.getKind()==kind::STRING_CONCAT ? b[i==0 ? 0 : b.getNumChildren()-1] : b;
        if( ac.isConst() && bc.isConst() ){
          CVC4::String as = ac.getConst<String>();
          CVC4::String bs = bc.getConst<String>();
          int slen = as.size() > bs.size() ? bs.size() : as.size();
          bool flag = i == 1 ? as.rstrncmp(bs, slen): as.strncmp(bs, slen);
          if(!flag) {
            return true;
          }
        }
      }
    }
    if( hasTerm( a ) && hasTerm( b ) ) {
      if( d_equalityEngine.areDisequal( a, b, false ) ){
        return true;
      }
    }
    return false;
  }
}

Node TheoryStrings::getLengthTerm( Node t ) {
  EqcInfo * ei = getOrMakeEqcInfo( t, false );
  Node length_term = ei ? ei->d_length_term : Node::null();
  if( length_term.isNull()) {
    //typically shouldnt be necessary
    length_term = t;
  }
  Debug("strings") << "TheoryStrings::getLengthTerm" << t << std::endl;
  return length_term;
}

Node TheoryStrings::getLength( Node t, bool use_t ) {
  Node retNode;
  if(t.isConst() || use_t) {
    retNode = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, t );
  } else {
    retNode = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, getLengthTerm( t ) );
  }
  return Rewriter::rewrite( retNode );
}

void TheoryStrings::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryStrings::addSharedTerm(TNode t) {
  Debug("strings") << "TheoryStrings::addSharedTerm(): "
                     << t << " " << t.getType().isBoolean() << endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_STRINGS);
  Debug("strings") << "TheoryStrings::addSharedTerm() finished" << std::endl;
}

EqualityStatus TheoryStrings::getEqualityStatus(TNode a, TNode b) {
  if( d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b) ){
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b, false)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  return EQUALITY_UNKNOWN;
}

void TheoryStrings::propagate(Effort e)
{
  // direct propagation now
}

bool TheoryStrings::propagate(TNode literal) {
  Debug("strings-propagate") << "TheoryStrings::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("strings-propagate") << "TheoryStrings::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}

/** explain */
void TheoryStrings::explain(TNode literal, std::vector<TNode>& assumptions){
  Debug("strings-explain") << "Explain " << literal << " " << d_conflict << std::endl;
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  unsigned ps = assumptions.size();
  std::vector< TNode > tassumptions;
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    if( atom[0]!=atom[1] ){
      d_equalityEngine.explainEquality(atom[0], atom[1], polarity, tassumptions);
    }
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, tassumptions);
  }
  for( unsigned i=0; i<tassumptions.size(); i++ ){
    if( std::find( assumptions.begin(), assumptions.end(), tassumptions[i] )==assumptions.end() ){
      assumptions.push_back( tassumptions[i] );
    }
  }
  Debug("strings-explain-debug") << "Explanation for " << literal << " was " << std::endl;
  for( unsigned i=ps; i<assumptions.size(); i++ ){
    Debug("strings-explain-debug") << "   " << assumptions[i] << std::endl;
  }
}

Node TheoryStrings::explain( TNode literal ){
  std::vector< TNode > assumptions;
  explain( literal, assumptions );
  if( assumptions.empty() ){
    return d_true;
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( kind::AND, assumptions );
  }
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::presolve() {
  Debug("strings-presolve") << "TheoryStrings::Presolving : get fmf options " << (options::stringFMF() ? "true" : "false") << std::endl;
  d_opt_fmf = options::stringFMF();

  if(!options::stdASCII()) {
    d_card_size = 256;
  }
}


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::collectModelInfo( TheoryModel* m, bool fullModel ) {
  Trace("strings-model") << "TheoryStrings : Collect model info, fullModel = " << fullModel << std::endl;
  Trace("strings-model") << "TheoryStrings : assertEqualityEngine." << std::endl;
  m->assertEqualityEngine( &d_equalityEngine );
  // Generate model
  std::vector< Node > nodes;
  getEquivalenceClasses( nodes );
  std::map< Node, Node > processed;
  std::vector< std::vector< Node > > col;
  std::vector< Node > lts;
  separateByLength( nodes, col, lts );
  //step 1 : get all values for known lengths
  std::vector< Node > lts_values;
  std::map< unsigned, bool > values_used;
  for( unsigned i=0; i<col.size(); i++ ) {
    Trace("strings-model") << "Checking length for {";
    for( unsigned j=0; j<col[i].size(); j++ ) {
      if( j>0 ) {
        Trace("strings-model") << ", ";
      }
      Trace("strings-model") << col[i][j];
    }
    Trace("strings-model") << " } (length is " << lts[i] << ")" << std::endl;
    if( lts[i].isConst() ) {
      lts_values.push_back( lts[i] );
      Assert(lts[i].getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string model");
      unsigned lvalue = lts[i].getConst<Rational>().getNumerator().toUnsignedInt();
      values_used[ lvalue ] = true;
    }else{
      //get value for lts[i];
      if( !lts[i].isNull() ){
        Node v = d_valuation.getModelValue(lts[i]);
        Trace("strings-model") << "Model value for " << lts[i] << " is " << v << std::endl;
        lts_values.push_back( v );
        Assert(v.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string model");
        unsigned lvalue =  v.getConst<Rational>().getNumerator().toUnsignedInt();
        values_used[ lvalue ] = true;
      }else{
        //Trace("strings-model-warn") << "No length for eqc " << col[i][0] << std::endl;
        //Assert( false );
        lts_values.push_back( Node::null() );
      }
    }
  }
  ////step 2 : assign arbitrary values for unknown lengths?
  // confirmed by calculus invariant, see paper
  //for( unsigned i=0; i<col.size(); i++ ){
  //  if(
  //}
  Trace("strings-model") << "Assign to equivalence classes..." << std::endl;
  //step 3 : assign values to equivalence classes that are pure variables
  for( unsigned i=0; i<col.size(); i++ ){
    std::vector< Node > pure_eq;
    Trace("strings-model") << "The equivalence classes ";
    for( unsigned j=0; j<col[i].size(); j++ ) {
      Trace("strings-model") << col[i][j] << " ";
      //check if col[i][j] has only variables
      EqcInfo* ei = getOrMakeEqcInfo( col[i][j], false );
      Node cst = ei ? ei->d_const_term : Node::null();
      if( cst.isNull() ){
        Assert( d_normal_forms.find( col[i][j] )!=d_normal_forms.end() );
        if( d_normal_forms[col[i][j]].size()==1 ){//&& d_normal_forms[col[i][j]][0]==col[i][j] ){
          pure_eq.push_back( col[i][j] );
        }
      }else{
        processed[col[i][j]] = cst;
      }
    }
    Trace("strings-model") << "have length " << lts_values[i] << std::endl;

    //assign a new length if necessary
    if( !pure_eq.empty() ){
      if( lts_values[i].isNull() ){
        unsigned lvalue = 0;
        while( values_used.find( lvalue )!=values_used.end() ){
          lvalue++;
        }
        Trace("strings-model") << "*** Decide to make length of " << lvalue << std::endl;
        lts_values[i] = NodeManager::currentNM()->mkConst( Rational( lvalue ) );
        values_used[ lvalue ] = true;
      }
      Trace("strings-model") << "Need to assign values of length " << lts_values[i] << " to equivalence classes ";
      for( unsigned j=0; j<pure_eq.size(); j++ ){
        Trace("strings-model") << pure_eq[j] << " ";
      }
      Trace("strings-model") << std::endl;


      //use type enumerator
      Assert(lts_values[i].getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string model");
      StringEnumeratorLength sel(lts_values[i].getConst<Rational>().getNumerator().toUnsignedInt());
      for( unsigned j=0; j<pure_eq.size(); j++ ){
        Assert( !sel.isFinished() );
        Node c = *sel;
        while( d_equalityEngine.hasTerm( c ) ){
          ++sel;
          Assert( !sel.isFinished() );
          c = *sel;
        }
        ++sel;
        Trace("strings-model") << "*** Assigned constant " << c << " for " << pure_eq[j] << std::endl;
        processed[pure_eq[j]] = c;
        m->assertEquality( pure_eq[j], c, true );
      }
    }
  }
  Trace("strings-model") << "String Model : Pure Assigned." << std::endl;
  //step 4 : assign constants to all other equivalence classes
  for( unsigned i=0; i<nodes.size(); i++ ){
    if( processed.find( nodes[i] )==processed.end() ){
      Assert( d_normal_forms.find( nodes[i] )!=d_normal_forms.end() );
      Trace("strings-model") << "Construct model for " << nodes[i] << " based on normal form ";
      for( unsigned j=0; j<d_normal_forms[nodes[i]].size(); j++ ) {
        if( j>0 ) Trace("strings-model") << " ++ ";
        Trace("strings-model") << d_normal_forms[nodes[i]][j];
        Node r = getRepresentative( d_normal_forms[nodes[i]][j] );
        if( !r.isConst() && processed.find( r )==processed.end() ){
          Trace("strings-model") << "(UNPROCESSED)";
        }
      }
      Trace("strings-model") << std::endl;
      std::vector< Node > nc;
      for( unsigned j=0; j<d_normal_forms[nodes[i]].size(); j++ ) {
        Node r = getRepresentative( d_normal_forms[nodes[i]][j] );
        Assert( r.isConst() || processed.find( r )!=processed.end() );
        nc.push_back(r.isConst() ? r : processed[r]);
      }
      Node cc = mkConcat( nc );
      Assert( cc.getKind()==kind::CONST_STRING );
      Trace("strings-model") << "*** Determined constant " << cc << " for " << nodes[i] << std::endl;
      processed[nodes[i]] = cc;
      m->assertEquality( nodes[i], cc, true );
    }
  }
  //Trace("strings-model") << "String Model : Assigned." << std::endl;
  Trace("strings-model") << "String Model : Finished." << std::endl;
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::preRegisterTerm(TNode n) {
  if( d_registered_terms_cache.find(n) == d_registered_terms_cache.end() ) {
    //check for logic exceptions
    if( !options::stringExp() ){
      if( n.getKind()==kind::STRING_STRIDOF ||
          n.getKind() == kind::STRING_ITOS || n.getKind() == kind::STRING_U16TOS || n.getKind() == kind::STRING_U32TOS ||
          n.getKind() == kind::STRING_STOI || n.getKind() == kind::STRING_STOU16 || n.getKind() == kind::STRING_STOU32 ||
          n.getKind() == kind::STRING_STRREPL || n.getKind() == kind::STRING_STRCTN ){
        std::stringstream ss;
        ss << "Term of kind " << n.getKind() << " not supported in default mode, try --strings-exp";
        throw LogicException(ss.str());
      }
    }
    switch( n.getKind() ) {
      case kind::EQUAL: {
        d_equalityEngine.addTriggerEquality(n);
        break;
      }
      case kind::STRING_IN_REGEXP: {
        d_out->requirePhase(n, true);
        d_equalityEngine.addTriggerPredicate(n);
        d_equalityEngine.addTerm(n[0]);
        d_equalityEngine.addTerm(n[1]);
        break;
      }
      //case kind::STRING_SUBSTR_TOTAL:
      default: {
        if( n.getType().isString() ) {
          registerTerm(n);
          // FMF
          if( n.getKind() == kind::VARIABLE && options::stringFMF() ) {
            d_input_vars.insert(n);
          }
        } else if (n.getType().isBoolean()) {
          // Get triggered for both equal and dis-equal
          d_equalityEngine.addTriggerPredicate(n);
        } else {
          // Function applications/predicates
          d_equalityEngine.addTerm(n);
        }
      }
    }
    d_registered_terms_cache.insert(n);
  }
}

Node TheoryStrings::expandDefinition(LogicRequest &logicRequest, Node node) {
  switch (node.getKind()) {
    case kind::STRING_CHARAT: {
      if(d_ufSubstr.isNull()) {
        std::vector< TypeNode > argTypes;
        argTypes.push_back(NodeManager::currentNM()->stringType());
        argTypes.push_back(NodeManager::currentNM()->integerType());
        argTypes.push_back(NodeManager::currentNM()->integerType());
        d_ufSubstr = NodeManager::currentNM()->mkSkolem("__ufSS",
                    NodeManager::currentNM()->mkFunctionType(
                               argTypes, NodeManager::currentNM()->stringType()),
                    "uf substr",
                    NodeManager::SKOLEM_EXACT_NAME);
      }
      Node lenxgti = NodeManager::currentNM()->mkNode( kind::GT,
                   NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, node[0] ), node[1] );
      Node t1greq0 = NodeManager::currentNM()->mkNode( kind::GEQ, node[1], d_zero);
      Node cond = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, lenxgti, t1greq0 ));
      Node totalf = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, node[0], node[1], d_one);
      Node uf = NodeManager::currentNM()->mkNode(kind::APPLY_UF, d_ufSubstr, node[0], node[1], d_one);
      return NodeManager::currentNM()->mkNode( kind::ITE, cond, totalf, uf );
      break;
    }

    case kind::STRING_SUBSTR: {
      if(d_ufSubstr.isNull()) {
        std::vector< TypeNode > argTypes;
        argTypes.push_back(NodeManager::currentNM()->stringType());
        argTypes.push_back(NodeManager::currentNM()->integerType());
        argTypes.push_back(NodeManager::currentNM()->integerType());
        d_ufSubstr = NodeManager::currentNM()->mkSkolem("__ufSS",
                    NodeManager::currentNM()->mkFunctionType(
                               argTypes, NodeManager::currentNM()->stringType()),
                    "uf substr",
                    NodeManager::SKOLEM_EXACT_NAME);
      }
      Node lenxgti = NodeManager::currentNM()->mkNode( kind::GEQ,
                   NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, node[0] ),
                   NodeManager::currentNM()->mkNode( kind::PLUS, node[1], node[2] ) );
      Node t1geq0 = NodeManager::currentNM()->mkNode(kind::GEQ, node[1], d_zero);
      Node t2geq0 = NodeManager::currentNM()->mkNode(kind::GEQ, node[2], d_zero);
      Node cond = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, lenxgti, t1geq0, t2geq0 ));
      Node totalf = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, node[0], node[1], node[2]);
      Node uf = NodeManager::currentNM()->mkNode(kind::APPLY_UF, d_ufSubstr, node[0], node[1], node[2]);
      return NodeManager::currentNM()->mkNode( kind::ITE, cond, totalf, uf );
      break;
    }

    default :
      return node;
  }

  Unreachable();
}


void TheoryStrings::check(Effort e) {
  if (done() && !fullEffort(e)) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  bool polarity;
  TNode atom;

  /*if(getLogicInfo().hasEverything()) {
    WarningOnce() << "WARNING: strings not supported in default configuration (ALL_SUPPORTED).\n"
      << "To suppress this warning in the future use proper logic symbol, e.g. (set-logic QF_S)." << std::endl;
  }
  }*/

  if( !done() && !hasTerm( d_emptyString ) ) {
    preRegisterTerm( d_emptyString );
  }

 // Trace("strings-process") << "Theory of strings, check : " << e << std::endl;
  Trace("strings-check") << "Theory of strings, check : " << e << std::endl;
  while ( !done() && !d_conflict ) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Trace("strings-assertion") << "get assertion: " << fact << endl;
    polarity = fact.getKind() != kind::NOT;
    atom = polarity ? fact : fact[0];

    //run preprocess on memberships
    bool addFact = true;
    if( options::stringLazyPreproc() ){
      NodeBoolMap::const_iterator it = d_preproc_cache.find( atom );
      if( it==d_preproc_cache.end() ){
        d_preproc_cache[ atom ] = true;
        std::vector< Node > new_nodes;
        Node res = d_preproc.decompose( atom, new_nodes );
        if( atom!=res ){
          //check if reduction/deduction
          std::vector< Node > subs_lhs;
          std::vector< Node > subs_rhs;
          subs_lhs.push_back( atom );
          subs_rhs.push_back( d_true );
          Node sres = res.substitute( subs_lhs.begin(), subs_lhs.end(), subs_rhs.begin(), subs_rhs.end() );
          sres = Rewriter::rewrite( sres );
          if( sres!=res ){
            Node plem = NodeManager::currentNM()->mkNode( kind::IMPLIES, atom, sres );
            plem = Rewriter::rewrite( plem );
            Trace("strings-assert") << "(assert " << plem << ")" << std::endl;
            d_out->lemma( plem );
            Trace("strings-pp-lemma") << "Preprocess impl lemma : " << plem << std::endl;
            Trace("strings-pp-lemma") << "...from " << fact << std::endl;
          }else{
            Trace("strings-assertion-debug") << "...preprocessed to : " << res << std::endl;
            Node plem = NodeManager::currentNM()->mkNode( kind::IFF, atom, res );
            plem = Rewriter::rewrite( plem );
            Trace("strings-assert") << "(assert " << plem << ")" << std::endl;
            d_out->lemma( plem );
            Trace("strings-pp-lemma") << "Preprocess eq lemma : " << plem << std::endl;
            Trace("strings-pp-lemma") << "...from " << fact << std::endl;
            //reduced by preprocess
            addFact = false;
            d_preproc_cache[ atom ] = false;
          }
        }else{
          Trace("strings-assertion-debug") << "...preprocess ok." << std::endl;
        }
        if( !new_nodes.empty() ){
          Node nnlem = new_nodes.size()==1 ? new_nodes[0] : NodeManager::currentNM()->mkNode( kind::AND, new_nodes );
          nnlem = Rewriter::rewrite( nnlem );
          Trace("strings-assertion-debug") << "...new nodes : " << nnlem << std::endl;
          Trace("strings-pp-lemma") << "Preprocess lemma : " << nnlem << std::endl;
          Trace("strings-pp-lemma") << "...from " << fact << std::endl;
          Trace("strings-assert") << "(assert " << nnlem << ")" << std::endl;
          d_out->lemma( nnlem );
        }
      }else{
        addFact = (*it).second;
      }
    }
    //assert pending fact
    if( addFact ){
      assertPendingFact( atom, polarity, fact );
    }
  }
  doPendingFacts();

  if( e == EFFORT_FULL && !d_conflict && !d_valuation.needCheck() ) {
    Trace("strings-check") << "Theory of strings full effort check " << std::endl;

    if(Trace.isOn("strings-eqc")) {
      for( unsigned t=0; t<2; t++ ) {
        eq::EqClassesIterator eqcs2_i = eq::EqClassesIterator( &d_equalityEngine );
        Trace("strings-eqc") << (t==0 ? "STRINGS:" : "OTHER:") << std::endl;
        while( !eqcs2_i.isFinished() ){
          Node eqc = (*eqcs2_i);
          bool print = (t==0 && eqc.getType().isString() ) || (t==1 && !eqc.getType().isString() );
          if (print) {
            eq::EqClassIterator eqc2_i = eq::EqClassIterator( eqc, &d_equalityEngine );
            Trace("strings-eqc") << "Eqc( " << eqc << " ) : { ";
            while( !eqc2_i.isFinished() ) {
              if( (*eqc2_i)!=eqc ){
                Trace("strings-eqc") << (*eqc2_i) << " ";
              }
              ++eqc2_i;
            }
            Trace("strings-eqc") << " } " << std::endl;
            EqcInfo * ei = getOrMakeEqcInfo( eqc, false );
            if( ei ){
              Trace("strings-eqc-debug") << "* Length term : " << ei->d_length_term.get() << std::endl;
              Trace("strings-eqc-debug") << "* Cardinality lemma k : " << ei->d_cardinality_lem_k.get() << std::endl;
              Trace("strings-eqc-debug") << "* Normalization length lemma : " << ei->d_normalized_length.get() << std::endl;
            }
          }
          ++eqcs2_i;
        }
        Trace("strings-eqc") << std::endl;
      }
      Trace("strings-eqc") << std::endl;
    }

    bool addedLemma = false;
    bool addedFact;
    d_congruent.clear();
    do{
      checkInit();
      Trace("strings-process") << "Done check init, addedFact = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
      if( !hasProcessed() ){
        checkExtendedFuncsEval();
        Trace("strings-process") << "Done check extended functions eval, addedFact = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
        if( !hasProcessed() ){
          checkNormalForms();
          Trace("strings-process") << "Done check normal forms, addedFact = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
          if( !hasProcessed() ){
            checkLengthsEqc();
            Trace("strings-process") << "Done check lengths, addedFact = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
            if( !hasProcessed() ){
              checkExtendedFuncs();
              Trace("strings-process") << "Done check extended functions, addedFact = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
              if( !hasProcessed() ){
                checkCardinality();
                Trace("strings-process") << "Done check cardinality, addedFact = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
                //if( !d_conflict && !addedFact ) {
                //  addedFact = checkExtendedFuncsReduction();
                //  Trace("strings-process") << "Done check extended functions reductions, addedFact = " << addedFact << ", d_conflict = " << d_conflict << std::endl;
                //}
              }
            }
          }
        }
      }
      //flush the facts
      addedFact = !d_pending.empty();
      addedLemma = !d_lemma_cache.empty();
      doPendingFacts();
      doPendingLemmas();
    }while( !d_conflict && !addedLemma && addedFact );

    Trace("strings-check") << "Theory of strings done full effort check " << addedLemma << " " << d_conflict << std::endl;
  }
  Trace("strings-check") << "Theory of strings, done check : " << e << std::endl;
  Assert( d_pending.empty() );
  Assert( d_lemma_cache.empty() );
}

bool TheoryStrings::hasProcessed() {
  return d_conflict || !d_lemma_cache.empty() || !d_pending.empty();
}

void TheoryStrings::addToExplanation( Node a, Node b, std::vector< Node >& exp ) {
  if( a!=b ){
    Assert( areEqual( a, b ) );
    exp.push_back( a.eqNode( b ) );
  }
}

TheoryStrings::EqcInfo::EqcInfo(  context::Context* c ) : d_const_term(c), d_length_term(c), d_cardinality_lem_k(c), d_normalized_length(c) {

}

TheoryStrings::EqcInfo * TheoryStrings::getOrMakeEqcInfo( Node eqc, bool doMake ) {
  std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( eqc );
  if( eqc_i==d_eqc_info.end() ){
    if( doMake ){
      EqcInfo* ei = new EqcInfo( getSatContext() );
      d_eqc_info[eqc] = ei;
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*eqc_i).second;
  }
}


/** Conflict when merging two constants */
void TheoryStrings::conflict(TNode a, TNode b){
  if( !d_conflict ){
    Debug("strings-conflict") << "Making conflict..." << std::endl;
    d_conflict = true;
    Node conflictNode;
    if (a.getKind() == kind::CONST_BOOLEAN) {
      conflictNode = explain( a.iffNode(b) );
    } else {
      conflictNode = explain( a.eqNode(b) );
    }
    Trace("strings-conflict") << "CONFLICT: Eq engine conflict : " << conflictNode << std::endl;
    d_out->conflict( conflictNode );
  }
}

/** called when a new equivalance class is created */
void TheoryStrings::eqNotifyNewClass(TNode t){
  if( t.getKind() == kind::CONST_STRING ){
    EqcInfo * ei =getOrMakeEqcInfo( t, true );
    ei->d_const_term = t;
  }
  if( t.getKind() == kind::STRING_LENGTH ){
    Trace("strings-debug") << "New length eqc : " << t << std::endl;
    Node r = d_equalityEngine.getRepresentative(t[0]);
    EqcInfo * ei = getOrMakeEqcInfo( r, true );
    ei->d_length_term = t[0];
  }
}

/** called when two equivalance classes will merge */
void TheoryStrings::eqNotifyPreMerge(TNode t1, TNode t2){
    EqcInfo * e2 = getOrMakeEqcInfo(t2, false);
    if( e2 ){
      EqcInfo * e1 = getOrMakeEqcInfo( t1 );
      //add information from e2 to e1
      if( !e2->d_const_term.get().isNull() ){
        e1->d_const_term.set( e2->d_const_term );
      }
      if( !e2->d_length_term.get().isNull() ){
        e1->d_length_term.set( e2->d_length_term );
      }
      if( e2->d_cardinality_lem_k.get()>e1->d_cardinality_lem_k.get() ) {
        e1->d_cardinality_lem_k.set( e2->d_cardinality_lem_k );
      }
      if( !e2->d_normalized_length.get().isNull() ){
        e1->d_normalized_length.set( e2->d_normalized_length );
      }
    }
    /*
    if( hasTerm( d_zero ) ){
      Node leqc;
      if( areEqual(d_zero, t1) ){
        leqc = t2;
      }else if( areEqual(d_zero, t2) ){
        leqc = t1;
      }
      if( !leqc.isNull() ){
        //scan equivalence class to see if we apply
        eq::EqClassIterator eqc_i = eq::EqClassIterator( leqc, &d_equalityEngine );
        while( !eqc_i.isFinished() ){
          Node n = (*eqc_i);
          if( n.getKind()==kind::STRING_LENGTH ){
            if( !hasTerm( d_emptyString ) || !areEqual(n[0], d_emptyString ) ){
              //apply the rule length(n[0])==0 => n[0] == ""
              Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, n[0], d_emptyString );
              d_pending.push_back( eq );
              Node eq_exp = NodeManager::currentNM()->mkNode( kind::EQUAL, n, d_zero );
              d_pending_exp[eq] = eq_exp;
              Trace("strings-infer") << "Strings : Infer Empty : " << eq << " from " << eq_exp << std::endl;
              d_infer.push_back(eq);
              d_infer_exp.push_back(eq_exp);
            }
          }
          ++eqc_i;
        }
      }
    }
    */
}

/** called when two equivalance classes have merged */
void TheoryStrings::eqNotifyPostMerge(TNode t1, TNode t2) {

}

/** called when two equivalance classes are disequal */
void TheoryStrings::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {

}

void TheoryStrings::computeCareGraph(){
  Theory::computeCareGraph();
}

void TheoryStrings::assertPendingFact(Node atom, bool polarity, Node exp) {
  Trace("strings-pending") << "Assert pending fact : " << atom << " " << polarity << " from " << exp << std::endl;
  Assert(atom.getKind() != kind::OR, "Infer error: a split.");
  if( atom.getKind()==kind::EQUAL ){
    //AJR : is this necessary?
    for( unsigned j=0; j<2; j++ ) {
      if( !d_equalityEngine.hasTerm( atom[j] ) && atom[j].getType().isString() ) {
        //TODO: check!!!
        registerTerm( atom[j] );
      }
    }
    d_equalityEngine.assertEquality( atom, polarity, exp );
  } else {
    if( atom.getKind()==kind::STRING_IN_REGEXP ) {
#ifdef LAZY_ADD_MEMBERSHIP
      if( d_ext_func_terms.find( atom )==d_ext_func_terms.end() ){
        Trace("strings-extf-debug") << "Found extended function (membership) : " << atom << std::endl;
        d_ext_func_terms[atom] = true;
      }
#else
      addMembership( polarity ? atom : atom.negate() );
#endif
    }
    d_equalityEngine.assertPredicate( atom, polarity, exp );
  }
  //collect extended function terms in the atom
  if( options::stringExp() ){
    std::map< Node, bool > visited;
    collectExtendedFuncTerms( atom, visited );
  }
}

void TheoryStrings::doPendingFacts() {
  size_t i=0;
  while( !d_conflict && i<d_pending.size() ) {
    Node fact = d_pending[i];
    Node exp = d_pending_exp[ fact ];
    if(fact.getKind() == kind::AND) {
      for(size_t j=0; j<fact.getNumChildren(); j++) {
        bool polarity = fact[j].getKind() != kind::NOT;
        TNode atom = polarity ? fact[j] : fact[j][0];
        assertPendingFact(atom, polarity, exp);
      }
    } else {
      bool polarity = fact.getKind() != kind::NOT;
      TNode atom = polarity ? fact : fact[0];
      assertPendingFact(atom, polarity, exp);
    }
    i++;
  }
  d_pending.clear();
  d_pending_exp.clear();
}

void TheoryStrings::doPendingLemmas() {
  if( !d_conflict && !d_lemma_cache.empty() ){
    for( unsigned i=0; i<d_lemma_cache.size(); i++ ){
      Trace("strings-pending") << "Process pending lemma : " << d_lemma_cache[i] << std::endl;
      d_out->lemma( d_lemma_cache[i] );
    }
    for( std::map< Node, bool >::iterator it = d_pending_req_phase.begin(); it != d_pending_req_phase.end(); ++it ){
      Trace("strings-pending") << "Require phase : " << it->first << ", polarity = " << it->second << std::endl;
      d_out->requirePhase( it->first, it->second );
    }
  }
  d_lemma_cache.clear();
  d_pending_req_phase.clear();
}

bool TheoryStrings::getNormalForms(Node &eqc, std::vector< Node > & visited, std::vector< Node > & nf,
  std::vector< std::vector< Node > > &normal_forms,  std::vector< std::vector< Node > > &normal_forms_exp, std::vector< Node > &normal_form_src) {
  Trace("strings-process-debug") << "Get normal forms " << eqc << std::endl;
  // EqcItr
  eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
  while( !eqc_i.isFinished() ) {
    Node n = (*eqc_i);
    if( std::find( d_congruent.begin(), d_congruent.end(), n )==d_congruent.end() ){
      if( n.getKind() == kind::CONST_STRING || n.getKind() == kind::STRING_CONCAT ) {
        Trace("strings-process-debug") << "Get Normal Form : Process term " << n << " in eqc " << eqc << std::endl;
        std::vector<Node> nf_n;
        std::vector<Node> nf_exp_n;
        bool result = true;
        if( n.getKind() == kind::CONST_STRING  ) {
          if( n!=d_emptyString ) {
            nf_n.push_back( n );
          }
        } else if( n.getKind() == kind::STRING_CONCAT ){
          for( unsigned i=0; i<n.getNumChildren(); i++ ) {
            Node nr = d_equalityEngine.getRepresentative( n[i] );
            std::vector< Node > nf_temp;
            std::vector< Node > nf_exp_temp;
            Trace("strings-process-debug") << "Normalizing subterm " << n[i] << " = "  << nr << std::endl;
            bool nresult = false;
            if( nr==eqc ) {
              nf_temp.push_back( nr );
            } else {
              nresult = normalizeEquivalenceClass( nr, visited, nf_temp, nf_exp_temp );
              if( hasProcessed() ) {
                return true;
              }
            }
            //successfully computed normal form
            if( nf.size()!=1 || nf[0]!=d_emptyString ) {
              if( Trace.isOn("strings-error") ) {
                for( unsigned r=0; r<nf_temp.size(); r++ ) {
                  if( nresult && nf_temp[r].getKind()==kind::STRING_CONCAT ) {
                    Trace("strings-error") << "Strings::Error: From eqc = " << eqc << ", " << n << " index " << i << ", bad normal form : ";
                    for( unsigned rr=0; rr<nf_temp.size(); rr++ ) {
                      Trace("strings-error") << nf_temp[rr] << " ";
                    }
                    Trace("strings-error") << std::endl;
                  }
                  Assert( !nresult || nf_temp[r].getKind()!=kind::STRING_CONCAT );
                }
              }
              nf_n.insert( nf_n.end(), nf_temp.begin(), nf_temp.end() );
            }
            nf_exp_n.insert( nf_exp_n.end(), nf_exp_temp.begin(), nf_exp_temp.end() );
            if( nr!=n[i] ) {
              nf_exp_n.push_back( n[i].eqNode( nr ) );
            }
            if( !nresult ) {
              //Trace("strings-process-debug") << "....Caused already asserted
              for( unsigned j=i+1; j<n.getNumChildren(); j++ ) {
                if( !areEqual( n[j], d_emptyString ) ) {
                  nf_n.push_back( n[j] );
                }
              }
              if( nf_n.size()>1 ) {
                result = false;
                break;
              }
            }
          }
        }
        //if not equal to self
        //if( nf_n.size()!=1 || (nf_n.size()>1 && nf_n[0]!=eqc ) ){
        if( nf_n.size()>1 || ( nf_n.size()==1 && nf_n[0].getKind()==kind::CONST_STRING ) ) {
          if( nf_n.size()>1 ) {
            Trace("strings-process-debug") << "Check for cycle lemma for normal form ";
            printConcat(nf_n,"strings-process-debug");
            Trace("strings-process-debug") << "..." << std::endl;
            for( unsigned i=0; i<nf_n.size(); i++ ) {
              //if a component is equal to whole,
              if( areEqual( nf_n[i], n ) ){
                //all others must be empty
                std::vector< Node > ant;
                if( nf_n[i]!=n ){
                  ant.push_back( nf_n[i].eqNode( n ) );
                }
                ant.insert( ant.end(), nf_exp_n.begin(), nf_exp_n.end() );
                std::vector< Node > cc;
                for( unsigned j=0; j<nf_n.size(); j++ ){
                  if( i!=j ){
                    cc.push_back( nf_n[j].eqNode( d_emptyString ) );
                  }
                }
                std::vector< Node > empty_vec;
                Node conc = cc.size()==1 ? cc[0] : NodeManager::currentNM()->mkNode( kind::AND, cc );
                conc = Rewriter::rewrite( conc );
                sendInfer( mkAnd( ant ), conc, "CYCLE" );
                return true;
              }
            }
          }
          if( !result ) {
            Trace("strings-process-debug") << "Will have cycle lemma at higher level!" << std::endl;
            //we have a normal form that will cause a component lemma at a higher level
            normal_forms.clear();
            normal_forms_exp.clear();
            normal_form_src.clear();
          }
          normal_forms.push_back(nf_n);
          normal_forms_exp.push_back(nf_exp_n);
          normal_form_src.push_back(n);
          if( !result ) {
            return false;
          }
        } else {
          Node nn = nf_n.size()==0 ? d_emptyString : nf_n[0];
          //Assert( areEqual( nf_n[0], eqc ) );
          if( !areEqual( nn, eqc ) ){
            std::vector< Node > ant;
            ant.insert( ant.end(), nf_exp_n.begin(), nf_exp_n.end() );
            ant.push_back( n.eqNode( eqc ) );
            Node conc = Rewriter::rewrite( nn.eqNode( eqc ) );
            sendInfer( mkAnd( ant ), conc, "CYCLE-T" );
            return true;
          }
        }
        //}
      }
    }
    ++eqc_i;
  }

  // Test the result
  if(Trace.isOn("strings-solve")) {
    if( !normal_forms.empty() ) {
      Trace("strings-solve") << "--- Normal forms for equivlance class " << eqc << " : " << std::endl;
      for( unsigned i=0; i<normal_forms.size(); i++ ) {
        Trace("strings-solve") << "#" << i << " (from " << normal_form_src[i] << ") : ";
        //mergeCstVec(normal_forms[i]);
        for( unsigned j=0; j<normal_forms[i].size(); j++ ) {
          if(j>0) {
            Trace("strings-solve") << ", ";
          }
          Trace("strings-solve") << normal_forms[i][j];
        }
        Trace("strings-solve") << std::endl;
        Trace("strings-solve") << "   Explanation is : ";
        if(normal_forms_exp[i].size() == 0) {
          Trace("strings-solve") << "NONE";
        } else {
          for( unsigned j=0; j<normal_forms_exp[i].size(); j++ ) {
            if(j>0) {
              Trace("strings-solve") << " AND ";
            }
            Trace("strings-solve") << normal_forms_exp[i][j];
          }
        }
        Trace("strings-solve") << std::endl;
      }
    } else {
      //std::vector< Node > nf;
      //nf.push_back( eqc );
      //normal_forms.push_back(nf);
      //std::vector< Node > nf_exp_def;
      //normal_forms_exp.push_back(nf_exp_def);
      //normal_form_src.push_back(eqc);
      Trace("strings-solve") << "--- Single normal form for equivalence class " << eqc << std::endl;
    }
  }
  return true;
}

void TheoryStrings::mergeCstVec(std::vector< Node > &vec_strings) {
  std::vector< Node >::iterator itr = vec_strings.begin();
  while(itr != vec_strings.end()) {
    if(itr->isConst()) {
      std::vector< Node >::iterator itr2 = itr + 1;
      if(itr2 == vec_strings.end()) {
        break;
      } else if(itr2->isConst()) {
        CVC4::String s1 = itr->getConst<String>();
        CVC4::String s2 = itr2->getConst<String>();
        *itr = NodeManager::currentNM()->mkConst(s1.concat(s2));
        vec_strings.erase(itr2);
      } else {
        ++itr;
      }
    } else {
      ++itr;
    }
  }
}

bool TheoryStrings::detectLoop( std::vector< std::vector< Node > > &normal_forms,
  int i, int j, int index_i, int index_j,
  int &loop_in_i, int &loop_in_j) {
  int has_loop[2] = { -1, -1 };
  if( options::stringLB() != 2 ) {
    for( unsigned r=0; r<2; r++ ) {
      int index = (r==0 ? index_i : index_j);
      int other_index = (r==0 ? index_j : index_i );
      int n_index = (r==0 ? i : j);
      int other_n_index = (r==0 ? j : i);
      if( normal_forms[other_n_index][other_index].getKind() != kind::CONST_STRING ) {
        for( unsigned lp = index+1; lp<normal_forms[n_index].size(); lp++ ){
          if( normal_forms[n_index][lp]==normal_forms[other_n_index][other_index] ){
            has_loop[r] = lp;
            break;
          }
        }
      }
    }
  }
  if( has_loop[0]!=-1 || has_loop[1]!=-1 ) {
    loop_in_i = has_loop[0];
    loop_in_j = has_loop[1];
    return true;
  } else {
    return false;
  }
}
//xs(zy)=t(yz)xr
bool TheoryStrings::processLoop(std::vector< Node > &antec,
  std::vector< std::vector< Node > > &normal_forms,
  std::vector< Node > &normal_form_src,
  int i, int j, int loop_n_index, int other_n_index,
  int loop_index, int index, int other_index) {
  Node conc;
  Trace("strings-loop") << "Detected possible loop for " << normal_forms[loop_n_index][loop_index] << std::endl;
  Trace("strings-loop") << " ... (X)= " << normal_forms[other_n_index][other_index] << std::endl;

  Trace("strings-loop") << " ... T(Y.Z)= ";
  std::vector< Node > vec_t;
  for(int lp=index; lp<loop_index; ++lp) {
    if(lp != index) Trace("strings-loop") << " ++ ";
    Trace("strings-loop") << normal_forms[loop_n_index][lp];
    vec_t.push_back( normal_forms[loop_n_index][lp] );
  }
  Node t_yz = mkConcat( vec_t );
  Trace("strings-loop") << " (" << t_yz << ")" << std::endl;
  Trace("strings-loop") << " ... S(Z.Y)= ";
  std::vector< Node > vec_s;
  for(int lp=other_index+1; lp<(int)normal_forms[other_n_index].size(); ++lp) {
    if(lp != other_index+1) Trace("strings-loop") << " ++ ";
    Trace("strings-loop") << normal_forms[other_n_index][lp];
    vec_s.push_back( normal_forms[other_n_index][lp] );
  }
  Node s_zy = mkConcat( vec_s );
  Trace("strings-loop") << " (" << s_zy << ")" << std::endl;
  Trace("strings-loop") << " ... R= ";
  std::vector< Node > vec_r;
  for(int lp=loop_index+1; lp<(int)normal_forms[loop_n_index].size(); ++lp) {
    if(lp != loop_index+1) Trace("strings-loop") << " ++ ";
    Trace("strings-loop") << normal_forms[loop_n_index][lp];
    vec_r.push_back( normal_forms[loop_n_index][lp] );
  }
  Node r = mkConcat( vec_r );
  Trace("strings-loop") << " (" << r << ")" << std::endl;

  //Trace("strings-loop") << "Lemma Cache: " << normal_form_src[i] << " vs " << normal_form_src[j] << std::endl;
  //TODO: can be more general
  if( s_zy.isConst() && r.isConst() && r != d_emptyString) {
    int c;
    bool flag = true;
    if(s_zy.getConst<String>().tailcmp( r.getConst<String>(), c ) ) {
      if(c >= 0) {
        s_zy = NodeManager::currentNM()->mkConst( s_zy.getConst<String>().substr(0, c) );
        r = d_emptyString;
        vec_r.clear();
        Trace("strings-loop") << "Strings::Loop: Refactor S(Z.Y)= " << s_zy << ", c=" << c << std::endl;
        flag = false;
      }
    }
    if(flag) {
      Trace("strings-loop") << "Strings::Loop: tails are different." << std::endl;
      sendLemma( mkExplain( antec ), conc, "Loop Conflict" );
      return true;
    }
  }

  //require that x is non-empty
  if( !areDisequal( normal_forms[loop_n_index][loop_index], d_emptyString ) ){
    //try to make normal_forms[loop_n_index][loop_index] equal to empty to avoid loop
    sendSplit( normal_forms[loop_n_index][loop_index], d_emptyString, "Len-Split(Loop-X)" );
  } else if( !areDisequal( t_yz, d_emptyString ) && t_yz.getKind()!=kind::CONST_STRING  ) {
    //try to make normal_forms[loop_n_index][loop_index] equal to empty to avoid loop
    sendSplit( t_yz, d_emptyString, "Len-Split(Loop-YZ)" );
  } else {
    //need to break
    antec.push_back( normal_forms[loop_n_index][loop_index].eqNode( d_emptyString ).negate() );
    if( t_yz.getKind()!=kind::CONST_STRING ) {
      antec.push_back( t_yz.eqNode( d_emptyString ).negate() );
    }
    Node ant = mkExplain( antec );
    if(d_loop_antec.find(ant) == d_loop_antec.end()) {
      d_loop_antec.insert(ant);

      Node str_in_re;
      if( s_zy == t_yz &&
        r == d_emptyString &&
        s_zy.isConst() &&
        s_zy.getConst<String>().isRepeated()
        ) {
        Node rep_c = NodeManager::currentNM()->mkConst( s_zy.getConst<String>().substr(0, 1) );
        Trace("strings-loop") << "Special case (X)=" << normal_forms[other_n_index][other_index] << " " << std::endl;
        Trace("strings-loop") << "... (C)=" << rep_c << " " << std::endl;
        //special case
        str_in_re = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, normal_forms[other_n_index][other_index],
                NodeManager::currentNM()->mkNode( kind::REGEXP_STAR,
                NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, rep_c ) ) );
        conc = str_in_re;
      } else if(t_yz.isConst()) {
        Trace("strings-loop") << "Strings::Loop: Const Normal Breaking." << std::endl;
        CVC4::String s = t_yz.getConst< CVC4::String >();
        unsigned size = s.size();
        std::vector< Node > vconc;
        for(unsigned len=1; len<=size; len++) {
          Node y = NodeManager::currentNM()->mkConst(s.substr(0, len));
          Node z = NodeManager::currentNM()->mkConst(s.substr(len, size - len));
          Node restr = s_zy;
          Node cc;
          if(r != d_emptyString) {
            std::vector< Node > v2(vec_r);
            v2.insert(v2.begin(), y);
            v2.insert(v2.begin(), z);
            restr = mkConcat( z, y );
            cc = Rewriter::rewrite(s_zy.eqNode( mkConcat( v2 ) ));
          } else {
            cc = Rewriter::rewrite(s_zy.eqNode( mkConcat( z, y) ));
          }
          if(cc == d_false) {
            continue;
          }
          Node conc2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, normal_forms[other_n_index][other_index],
                  NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT,
                    NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, y),
                    NodeManager::currentNM()->mkNode(kind::REGEXP_STAR,
                      NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, restr))));
          cc = cc==d_true ? conc2 : NodeManager::currentNM()->mkNode( kind::AND, cc, conc2 );
          d_regexp_ant[conc2] = ant;
          vconc.push_back(cc);
        }
        conc = vconc.size()==0 ? Node::null() : vconc.size()==1 ? vconc[0] : NodeManager::currentNM()->mkNode(kind::OR, vconc);
      } else {
        Trace("strings-loop") << "Strings::Loop: Normal Loop Breaking." << std::endl;
        //right
        Node sk_w= mkSkolemS( "w_loop" );
        Node sk_y= mkSkolemS( "y_loop", 1 );
        Node sk_z= mkSkolemS( "z_loop" );
        //t1 * ... * tn = y * z
        Node conc1 = t_yz.eqNode( mkConcat( sk_y, sk_z ) );
        // s1 * ... * sk = z * y * r
        vec_r.insert(vec_r.begin(), sk_y);
        vec_r.insert(vec_r.begin(), sk_z);
        Node conc2 = s_zy.eqNode( mkConcat( vec_r ) );
        Node conc3 = normal_forms[other_n_index][other_index].eqNode( mkConcat( sk_y, sk_w ) );
        Node restr = r == d_emptyString ? s_zy : mkConcat( sk_z, sk_y );
        str_in_re = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, sk_w,
                NodeManager::currentNM()->mkNode( kind::REGEXP_STAR,
                  NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, restr ) ) );

        std::vector< Node > vec_conc;
        vec_conc.push_back(conc1); vec_conc.push_back(conc2); vec_conc.push_back(conc3);
        vec_conc.push_back(str_in_re);
        //vec_conc.push_back(sk_y.eqNode(d_emptyString).negate());//by mkskolems
        conc = NodeManager::currentNM()->mkNode( kind::AND, vec_conc );
      } // normal case

      //set its antecedant to ant, to say when it is relevant
      if(!str_in_re.isNull()) {
        d_regexp_ant[str_in_re] = ant;
      }

      sendLemma( ant, conc, "F-LOOP" );
      ++(d_statistics.d_loop_lemmas);

      //we will be done
      addNormalFormPair( normal_form_src[i], normal_form_src[j] );
    } else {
      Trace("strings-loop") << "Strings::Loop: loop lemma for " << ant << " has already added." << std::endl;
      addNormalFormPair( normal_form_src[i], normal_form_src[j] );
      return false;
    }
  }
  return true;
}
Node TheoryStrings::mkSkolemSplit( Node a, Node b, const char * c, int isLenSplit ){
  //return mkSkolemS( c, isLenSplit );
  std::map< int, Node >::iterator it = d_skolem_cache[a][b].find( isLenSplit );
  if( it==d_skolem_cache[a][b].end() ){
    Node sk = mkSkolemS( c, isLenSplit );
    d_skolem_cache[a][b][isLenSplit] = sk;
    return sk;
  }else{
    return it->second;
  }

}

bool TheoryStrings::processNEqc(std::vector< std::vector< Node > > &normal_forms,
  std::vector< std::vector< Node > > &normal_forms_exp,
  std::vector< Node > &normal_form_src) {
  bool flag_lb = false;
  std::vector< Node > c_lb_exp;
  int c_i, c_j, c_loop_n_index, c_other_n_index, c_loop_index, c_index, c_other_index;
  for(unsigned i=0; i<normal_forms.size()-1; i++) {
    //unify each normalform[j] with normal_forms[i]
    for(unsigned j=i+1; j<normal_forms.size(); j++ ) {
      Trace("strings-solve") << "Strings: Process normal form #" << i << " against #" << j << "..." << std::endl;
      if( isNormalFormPair( normal_form_src[i], normal_form_src[j] ) ) {
        Trace("strings-solve") << "Strings: Already cached." << std::endl;
      } else {
        //the current explanation for why the prefix is equal
        std::vector< Node > curr_exp;
        curr_exp.insert(curr_exp.end(), normal_forms_exp[i].begin(), normal_forms_exp[i].end() );
        curr_exp.insert(curr_exp.end(), normal_forms_exp[j].begin(), normal_forms_exp[j].end() );
        if( normal_form_src[i]!=normal_form_src[j] ){
          curr_exp.push_back( normal_form_src[i].eqNode( normal_form_src[j] ) );
        }

        //process the reverse direction first (check for easy conflicts and inferences)
        if( processReverseNEq( normal_forms, normal_form_src, curr_exp, i, j ) ){
          return true;
        }

        //ensure that normal_forms[i] and normal_forms[j] are the same modulo equality
        unsigned index_i = 0;
        unsigned index_j = 0;
        bool success;
        do
        {
          //simple check
          if( processSimpleNEq( normal_forms, normal_form_src, curr_exp, i, j, index_i, index_j, false ) ){
            //added a lemma, return
            return true;
          }

          success = false;
          //if we are at the end
          if(index_i==normal_forms[i].size() || index_j==normal_forms[j].size() ) {
            Assert( index_i==normal_forms[i].size() && index_j==normal_forms[j].size() );
            //we're done
            //addNormalFormPair( normal_form_src[i], normal_form_src[j] );
          } else {
            Node length_term_i = getLength( normal_forms[i][index_i] );
            Node length_term_j = getLength( normal_forms[j][index_j] );
            //check  length(normal_forms[i][index]) == length(normal_forms[j][index])
            if( !areDisequal(length_term_i, length_term_j) &&
              !areEqual(length_term_i, length_term_j) &&
              normal_forms[i][index_i].getKind()!=kind::CONST_STRING &&
              normal_forms[j][index_j].getKind()!=kind::CONST_STRING ) {
              //length terms are equal, merge equivalence classes if not already done so
              Node length_eq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j );
              Trace("strings-solve-debug") << "Non-simple Case 1 : string lengths neither equal nor disequal" << std::endl;
              //try to make the lengths equal via splitting on demand
              sendSplit( length_term_i, length_term_j, "Len-Split(Diseq)" );
              length_eq = Rewriter::rewrite( length_eq  );
              d_pending_req_phase[ length_eq ] = true;
              return true;
            } else {
              Trace("strings-solve-debug") << "Non-simple Case 2 : must compare strings" << std::endl;
              int loop_in_i = -1;
              int loop_in_j = -1;
              if(detectLoop(normal_forms, i, j, index_i, index_j, loop_in_i, loop_in_j)) {
                if(!flag_lb) {
                  c_i = i;
                  c_j = j;
                  c_loop_n_index = loop_in_i!=-1 ? i : j;
                  c_other_n_index = loop_in_i!=-1 ? j : i;
                  c_loop_index = loop_in_i!=-1 ? loop_in_i : loop_in_j;
                  c_index = loop_in_i!=-1 ? index_i : index_j;
                  c_other_index = loop_in_i!=-1 ? index_j : index_i;

                  c_lb_exp = curr_exp;

                  if(options::stringLB() == 0) {
                    flag_lb = true;
                  } else {
                    if(processLoop(c_lb_exp, normal_forms, normal_form_src,
                      c_i, c_j, c_loop_n_index, c_other_n_index, c_loop_index, c_index, c_other_index)) {
                      return true;
                    }
                  }
                }
              } else {
                Node conc;
                std::vector< Node > antec;
                Trace("strings-solve-debug") << "No loops detected." << std::endl;
                if( normal_forms[i][index_i].getKind() == kind::CONST_STRING ||
                  normal_forms[j][index_j].getKind() == kind::CONST_STRING) {
                  unsigned const_k = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? i : j;
                  unsigned const_index_k = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? index_i : index_j;
                  unsigned nconst_k = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? j : i;
                  unsigned nconst_index_k = normal_forms[i][index_i].getKind() == kind::CONST_STRING ? index_j : index_i;
                  Node const_str = normal_forms[const_k][const_index_k];
                  Node other_str = normal_forms[nconst_k][nconst_index_k];
                  Assert( other_str.getKind()!=kind::CONST_STRING, "Other string is not constant." );
                  Assert( other_str.getKind()!=kind::STRING_CONCAT, "Other string is not CONCAT." );
                  if( !areDisequal(other_str, d_emptyString) ) {
                    sendSplit( other_str, d_emptyString, "Len-Split(CST)" );
                  } else {
                    Assert(areDisequal(other_str, d_emptyString), "CST Split on empty Var");
                    antec.insert( antec.end(), curr_exp.begin(), curr_exp.end() );
                    Node xnz = other_str.eqNode(d_emptyString).negate();
                    antec.push_back( xnz );
                    //Node sk = mkSkolemS( "c_spt" );
                    Node conc;
                    if( normal_forms[nconst_k].size() > nconst_index_k + 1 &&
                      normal_forms[nconst_k][nconst_index_k + 1].isConst() ) {
                      CVC4::String stra = const_str.getConst<String>();
                      CVC4::String strb = normal_forms[nconst_k][nconst_index_k + 1].getConst<String>();
                      CVC4::String stra1 = stra.substr(1);
                      size_t p = stra.size() - stra1.overlap(strb);
                      size_t p2 = stra1.find(strb);
                      p = p2==std::string::npos? p : ( p>p2+1? p2+1 : p );
                      Node prea = p==stra.size()? const_str : NodeManager::currentNM()->mkConst(stra.substr(0, p));
                      Node sk = mkSkolemSplit( other_str, prea, "c_spt" );
                      conc = other_str.eqNode( mkConcat(prea, sk) );
                      Trace("strings-csp") << "Const Split: " << prea << " is removed from " << stra << " due to " << strb << std::endl;
                    } else {
                      // normal v/c split
                      Node firstChar = const_str.getConst<String>().size() == 1 ? const_str :
                        NodeManager::currentNM()->mkConst( const_str.getConst<String>().substr(0, 1) );
                      Node sk = mkSkolemSplit( other_str, firstChar, "c_spt" );
                      conc = other_str.eqNode( mkConcat(firstChar, sk) );
                      Trace("strings-csp") << "Const Split: " << firstChar << " is removed from " << const_str << " (normal) " << std::endl;
                    }

                    conc = Rewriter::rewrite( conc );
                    sendLemma( mkExplain( antec ), conc, "S-Split(CST-P)" );
                    //sendInfer(mkAnd( antec ), conc, "S-Split(CST-P)");
                  }
                  return true;
                } else {
                  std::vector< Node > antec_new_lits;
                  antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );

                  Node ldeq = NodeManager::currentNM()->mkNode( kind::EQUAL, length_term_i, length_term_j ).negate();
                  if( d_equalityEngine.areDisequal( length_term_i, length_term_j, true ) ){
                    antec.push_back( ldeq );
                  }else{
                    antec_new_lits.push_back(ldeq);
                  }

                  //x!=e /\ y!=e
                  for(unsigned xory=0; xory<2; xory++) {
                    Node x = xory==0 ? normal_forms[i][index_i] : normal_forms[j][index_j];
                    Node xgtz = x.eqNode( d_emptyString ).negate();
                    if( d_equalityEngine.areDisequal( x, d_emptyString, true ) ) {
                      antec.push_back( xgtz );
                    } else {
                      antec_new_lits.push_back( xgtz );
                    }
                  }

                  //Node sk = mkSkolemS( "v_spt", 1 );
                  Node sk = mkSkolemSplit( normal_forms[i][index_i], normal_forms[j][index_j], "v_spt", 1 );
                  Node eq1 = normal_forms[i][index_i].eqNode( mkConcat(normal_forms[j][index_j], sk) );
                  Node eq2 = normal_forms[j][index_j].eqNode( mkConcat(normal_forms[i][index_i], sk) );
                  conc = Rewriter::rewrite(NodeManager::currentNM()->mkNode( kind::OR, eq1, eq2 ));

                  Node ant = mkExplain( antec, antec_new_lits );
                  sendLemma( ant, conc, "S-Split(VAR)" );
                  //sendInfer( ant, conc, "S-Split(VAR)" );
                  //++(d_statistics.d_eq_splits);
                  return true;
                }
              }
            }
          }
        } while(success);
      }
    }
    if(!flag_lb) {
      return false;
    }
  }
  if(flag_lb) {
    if(processLoop(c_lb_exp, normal_forms, normal_form_src,
      c_i, c_j, c_loop_n_index, c_other_n_index, c_loop_index, c_index, c_other_index)) {
      return true;
    }
  }

  return false;
}

bool TheoryStrings::processReverseNEq( std::vector< std::vector< Node > > &normal_forms,
  std::vector< Node > &normal_form_src, std::vector< Node > &curr_exp, unsigned i, unsigned j ) {
  //reverse normal form of i, j
  std::reverse( normal_forms[i].begin(), normal_forms[i].end() );
  std::reverse( normal_forms[j].begin(), normal_forms[j].end() );

  std::vector< Node > t_curr_exp;
  t_curr_exp.insert( t_curr_exp.begin(), curr_exp.begin(), curr_exp.end() );
  unsigned index_i = 0;
  unsigned index_j = 0;
  bool ret = processSimpleNEq( normal_forms, normal_form_src, t_curr_exp, i, j, index_i, index_j, true );

  //reverse normal form of i, j
  std::reverse( normal_forms[i].begin(), normal_forms[i].end() );
  std::reverse( normal_forms[j].begin(), normal_forms[j].end() );

  return ret;
}

bool TheoryStrings::processSimpleNEq( std::vector< std::vector< Node > > &normal_forms,
  std::vector< Node > &normal_form_src, std::vector< Node > &curr_exp,
  unsigned i, unsigned j, unsigned& index_i, unsigned& index_j, bool isRev ) {
  bool success;
  do {
    success = false;
    //if we are at the end
    if(index_i==normal_forms[i].size() || index_j==normal_forms[j].size() ) {
      if( index_i==normal_forms[i].size() && index_j==normal_forms[j].size() ) {
        //we're done
      } else {
        //the remainder must be empty
        unsigned k = index_i==normal_forms[i].size() ? j : i;
        unsigned index_k = index_i==normal_forms[i].size() ? index_j : index_i;
        Node eq_exp = mkAnd( curr_exp );
        while(!d_conflict && index_k<normal_forms[k].size()) {
          //can infer that this string must be empty
          Node eq = normal_forms[k][index_k].eqNode( d_emptyString );
          //Trace("strings-lemma") << "Strings: Infer " << eq << " from " << eq_exp << std::endl;
          Assert( !areEqual( d_emptyString, normal_forms[k][index_k] ) );
          sendInfer( eq_exp, eq, "EQ_Endpoint" );
          index_k++;
        }
        return true;
      }
    }else{
      Trace("strings-solve-debug") << "Process " << normal_forms[i][index_i] << " ... " << normal_forms[j][index_j] << std::endl;
      if(areEqual(normal_forms[i][index_i], normal_forms[j][index_j])) {
        Trace("strings-solve-debug") << "Simple Case 1 : strings are equal" << std::endl;
        //terms are equal, continue
        if( normal_forms[i][index_i]!=normal_forms[j][index_j] ){
          Node eq = normal_forms[i][index_i].eqNode(normal_forms[j][index_j]);
          Trace("strings-solve-debug") << "Add to explanation : " << eq << std::endl;
          curr_exp.push_back(eq);
        }
        index_j++;
        index_i++;
        success = true;
      } else {
        Node length_term_i = getLength( normal_forms[i][index_i] );
        Node length_term_j = getLength( normal_forms[j][index_j] );
        //check  length(normal_forms[i][index]) == length(normal_forms[j][index])
        if( areEqual(length_term_i, length_term_j) ) {
          Trace("strings-solve-debug") << "Simple Case 2 : string lengths are equal" << std::endl;
          Node eq = normal_forms[i][index_i].eqNode( normal_forms[j][index_j] );
          //eq = Rewriter::rewrite( eq );
          Node length_eq = length_term_i.eqNode( length_term_j );
          std::vector< Node > temp_exp;
          temp_exp.insert(temp_exp.end(), curr_exp.begin(), curr_exp.end() );
          temp_exp.push_back(length_eq);
          //must add explanation for length terms
          if( !normal_forms[i][index_i].isConst() && !length_term_i.isConst() && length_term_i[0]!=normal_forms[i][index_i] ){
            temp_exp.push_back( length_term_i[0].eqNode( normal_forms[i][index_i] ) );
          }
          if( !normal_forms[j][index_j].isConst() && !length_term_j.isConst() && length_term_j[0]!=normal_forms[j][index_j] ){
            temp_exp.push_back( length_term_j[0].eqNode( normal_forms[j][index_j] ) );
          }
          Node eq_exp = mkAnd( temp_exp );
          sendInfer( eq_exp, eq, "LengthEq" );
          return true;
        } else if(( normal_forms[i][index_i].getKind()!=kind::CONST_STRING && index_i==normal_forms[i].size()-1 ) ||
              ( normal_forms[j][index_j].getKind()!=kind::CONST_STRING && index_j==normal_forms[j].size()-1 ) ) {
          Trace("strings-solve-debug") << "Simple Case 3 : at endpoint" << std::endl;
          Node conc;
          std::vector< Node > antec;
          antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
          std::vector< Node > eqn;
          for( unsigned r=0; r<2; r++ ) {
            int index_k = r==0 ? index_i : index_j;
            int k = r==0 ? i : j;
            std::vector< Node > eqnc;
            for( unsigned index_l=index_k; index_l<normal_forms[k].size(); index_l++ ) {
              if(isRev) {
                eqnc.insert(eqnc.begin(), normal_forms[k][index_l] );
              } else {
                eqnc.push_back( normal_forms[k][index_l] );
              }
            }
            eqn.push_back( mkConcat( eqnc ) );
          }
          if( !areEqual( eqn[0], eqn[1] ) ) {
            conc = eqn[0].eqNode( eqn[1] );
            sendLemma( mkExplain( antec ), conc, "ENDPOINT" );
            //sendInfer( mkAnd( antec ), conc, "ENDPOINT" );
            return true;
          }else{
            index_i = normal_forms[i].size();
            index_j = normal_forms[j].size();
          }
        } else if(normal_forms[i][index_i].isConst() && normal_forms[j][index_j].isConst()) {
          Node const_str = normal_forms[i][index_i];
          Node other_str = normal_forms[j][index_j];
          Trace("strings-solve-debug") << "Simple Case 3 : Const Split : " << const_str << " vs " << other_str << std::endl;
          unsigned len_short = const_str.getConst<String>().size() <= other_str.getConst<String>().size() ? const_str.getConst<String>().size() : other_str.getConst<String>().size();
          bool isSameFix = isRev ? const_str.getConst<String>().rstrncmp(other_str.getConst<String>(), len_short): const_str.getConst<String>().strncmp(other_str.getConst<String>(), len_short);
          if( isSameFix ) {
            //same prefix/suffix
            //k is the index of the string that is shorter
            int k = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? i : j;
            int index_k = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? index_i : index_j;
            int l = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? j : i;
            int index_l = const_str.getConst<String>().size()<other_str.getConst<String>().size() ? index_j : index_i;
            if(isRev) {
              int new_len = normal_forms[l][index_l].getConst<String>().size() - len_short;
              Node remainderStr = NodeManager::currentNM()->mkConst( normal_forms[l][index_l].getConst<String>().substr(0, new_len) );
              Trace("strings-solve-debug-test") << "Break normal form of " << normal_forms[l][index_l] << " into " << normal_forms[k][index_k] << ", " << remainderStr << std::endl;
              normal_forms[l].insert( normal_forms[l].begin()+index_l + 1, remainderStr );
            } else {
              Node remainderStr = NodeManager::currentNM()->mkConst(normal_forms[l][index_l].getConst<String>().substr(len_short));
              Trace("strings-solve-debug-test") << "Break normal form of " << normal_forms[l][index_l] << " into " << normal_forms[k][index_k] << ", " << remainderStr << std::endl;
              normal_forms[l].insert( normal_forms[l].begin()+index_l + 1, remainderStr );
            }
            normal_forms[l][index_l] = normal_forms[k][index_k];
            index_i++;
            index_j++;
            success = true;
          } else {
            std::vector< Node > antec;
            //curr_exp is conflict
            antec.insert(antec.end(), curr_exp.begin(), curr_exp.end() );
            Node ant = mkExplain( antec );
            sendLemma( ant, d_false, "Const Conflict" );
            return true;
          }
        }
      }
    }
  }while( success );
  return false;
}


//nf_exp is conjunction
bool TheoryStrings::normalizeEquivalenceClass( Node eqc, std::vector< Node > & visited, std::vector< Node > & nf, std::vector< Node > & nf_exp ) {
  Trace("strings-process-debug") << "Process equivalence class " << eqc << std::endl;
  if( std::find( visited.begin(), visited.end(), eqc )!=visited.end() ){
    getConcatVec( eqc, nf );
    Trace("strings-process-debug") << "Return process equivalence class " << eqc << " : already visited." << std::endl;
    return false;
  } else if( areEqual( eqc, d_emptyString ) ) {
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ) {
      Node n = (*eqc_i);
      if( std::find( d_congruent.begin(), d_congruent.end(), n )==d_congruent.end() ){
        if( n.getKind()==kind::STRING_CONCAT ){
          //std::vector< Node > exp;
          //exp.push_back( n.eqNode( d_emptyString ) );
          //Node ant = mkExplain( exp );
          Node ant = n.eqNode( d_emptyString );
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            if( !areEqual( n[i], d_emptyString ) ){
              //sendLemma( ant, n[i].eqNode( d_emptyString ), "CYCLE" );
              sendInfer( ant, n[i].eqNode( d_emptyString ), "CYCLE" );
            }
          }
        }
      }
      ++eqc_i;
    }
    //do nothing
    Trace("strings-process-debug") << "Return process equivalence class " << eqc << " : empty." << std::endl;
    d_normal_forms_base[eqc] = d_emptyString;
    d_normal_forms[eqc].clear();
    d_normal_forms_exp[eqc].clear();
    return true;
  } else {
    visited.push_back( eqc );
    bool result;
    if(d_normal_forms.find(eqc)==d_normal_forms.end() ) {
      //phi => t = s1 * ... * sn
      // normal form for each non-variable term in this eqc (s1...sn)
      std::vector< std::vector< Node > > normal_forms;
      // explanation for each normal form (phi)
      std::vector< std::vector< Node > > normal_forms_exp;
      // record terms for each normal form (t)
      std::vector< Node > normal_form_src;
      //Get Normal Forms
      result = getNormalForms(eqc, visited, nf, normal_forms, normal_forms_exp, normal_form_src);
      if( hasProcessed() ) {
          return true;
      } else if( result ) {
        if(processNEqc(normal_forms, normal_forms_exp, normal_form_src)) {
          return true;
        }
      }

      //construct the normal form
      if( normal_forms.empty() ){
        Trace("strings-solve-debug2") << "construct the normal form" << std::endl;
        getConcatVec( eqc, nf );
      } else {
        Trace("strings-solve-debug2") << "just take the first normal form" << std::endl;
        //just take the first normal form
        nf.insert( nf.end(), normal_forms[0].begin(), normal_forms[0].end() );
        nf_exp.insert( nf_exp.end(), normal_forms_exp[0].begin(), normal_forms_exp[0].end() );
        if( eqc!=normal_form_src[0] ){
          nf_exp.push_back( eqc.eqNode( normal_form_src[0] ) );
        }
        Trace("strings-solve-debug2") << "just take the first normal form ... done" << std::endl;
      }

      d_normal_forms_base[eqc] = normal_form_src.empty() ? eqc : normal_form_src[0];
      d_normal_forms[eqc].insert( d_normal_forms[eqc].end(), nf.begin(), nf.end() );
      d_normal_forms_exp[eqc].insert( d_normal_forms_exp[eqc].end(), nf_exp.begin(), nf_exp.end() );
      Trace("strings-process-debug") << "Return process equivalence class " << eqc << " : returned, size = " << nf.size() << std::endl;
    } else {
      Trace("strings-process-debug") << "Return process equivalence class " << eqc << " : already computed, size = " << d_normal_forms[eqc].size() << std::endl;
      nf.insert( nf.end(), d_normal_forms[eqc].begin(), d_normal_forms[eqc].end() );
      nf_exp.insert( nf_exp.end(), d_normal_forms_exp[eqc].begin(), d_normal_forms_exp[eqc].end() );
      result = true;
    }
    visited.pop_back();
    return result;
  }
}

//return true for lemma, false if we succeed
bool TheoryStrings::processDeq( Node ni, Node nj ) {
  //Assert( areDisequal( ni, nj ) );
  if( d_normal_forms[ni].size()>1 || d_normal_forms[nj].size()>1 ){
    std::vector< Node > nfi;
    nfi.insert( nfi.end(), d_normal_forms[ni].begin(), d_normal_forms[ni].end() );
    std::vector< Node > nfj;
    nfj.insert( nfj.end(), d_normal_forms[nj].begin(), d_normal_forms[nj].end() );

    int revRet = processReverseDeq( nfi, nfj, ni, nj );
    if( revRet!=0 ){
      return revRet==-1;
    }

    nfi.clear();
    nfi.insert( nfi.end(), d_normal_forms[ni].begin(), d_normal_forms[ni].end() );
    nfj.clear();
    nfj.insert( nfj.end(), d_normal_forms[nj].begin(), d_normal_forms[nj].end() );

    unsigned index = 0;
    while( index<nfi.size() || index<nfj.size() ){
      int ret = processSimpleDeq( nfi, nfj, ni, nj, index, false );
      if( ret!=0 ) {
        return ret==-1;
      } else {
        Assert( index<nfi.size() && index<nfj.size() );
        Node i = nfi[index];
        Node j = nfj[index];
        Trace("strings-solve-debug")  << "...Processing(DEQ) " << i << " " << j << std::endl;
        if( !areEqual( i, j ) ) {
          Assert( i.getKind()!=kind::CONST_STRING || j.getKind()!=kind::CONST_STRING );
          Node li = getLength( i );
          Node lj = getLength( j );
          if( areDisequal(li, lj) ){
            //if( i.getKind()==kind::CONST_STRING || j.getKind()==kind::CONST_STRING ){

            Trace("strings-solve") << "Non-Simple Case 1 : add lemma " << std::endl;
            //must add lemma
            std::vector< Node > antec;
            std::vector< Node > antec_new_lits;
            antec.insert( antec.end(), d_normal_forms_exp[ni].begin(), d_normal_forms_exp[ni].end() );
            antec.insert( antec.end(), d_normal_forms_exp[nj].begin(), d_normal_forms_exp[nj].end() );
            //check disequal
            if( areDisequal( ni, nj ) ){
              antec.push_back( ni.eqNode( nj ).negate() );
            }else{
              antec_new_lits.push_back( ni.eqNode( nj ).negate() );
            }
            antec_new_lits.push_back( li.eqNode( lj ).negate() );
            std::vector< Node > conc;
            Node sk1 = mkSkolemS( "x_dsplit" );
            Node sk2 = mkSkolemS( "y_dsplit" );
            Node sk3 = mkSkolemS( "z_dsplit", 1 );
            //Node nemp = sk3.eqNode(d_emptyString).negate();
            //conc.push_back(nemp);
            Node lsk1 = getLength( sk1 );
            conc.push_back( lsk1.eqNode( li ) );
            Node lsk2 = getLength( sk2 );
            conc.push_back( lsk2.eqNode( lj ) );
            conc.push_back( NodeManager::currentNM()->mkNode( kind::OR,
                      j.eqNode( mkConcat( sk1, sk3 ) ), i.eqNode( mkConcat( sk2, sk3 ) ) ) );

            sendLemma( mkExplain( antec, antec_new_lits ), NodeManager::currentNM()->mkNode( kind::AND, conc ), "D-DISL-Split" );
            ++(d_statistics.d_deq_splits);
            return true;
          }else if( areEqual( li, lj ) ){
            Assert( !areDisequal( i, j ) );
            //splitting on demand : try to make them disequal
            Node eq = i.eqNode( j );
            sendSplit( i, j, "S-Split(DEQL)" );
            eq = Rewriter::rewrite( eq );
            d_pending_req_phase[ eq ] = false;
            return true;
          }else{
            //splitting on demand : try to make lengths equal
            Node eq = li.eqNode( lj );
            sendSplit( li, lj, "D-Split" );
            eq = Rewriter::rewrite( eq );
            d_pending_req_phase[ eq ] = true;
            return true;
          }
        }
        index++;
      }
    }
    Assert( false );
  }
  return false;
}

int TheoryStrings::processReverseDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj ) {
  //reverse normal form of i, j
  std::reverse( nfi.begin(), nfi.end() );
  std::reverse( nfj.begin(), nfj.end() );

  unsigned index = 0;
  int ret = processSimpleDeq( nfi, nfj, ni, nj, index, true );

  //reverse normal form of i, j
  std::reverse( nfi.begin(), nfi.end() );
  std::reverse( nfj.begin(), nfj.end() );

  return ret;
}

int TheoryStrings::processSimpleDeq( std::vector< Node >& nfi, std::vector< Node >& nfj, Node ni, Node nj, unsigned& index, bool isRev ) {
  while( index<nfi.size() || index<nfj.size() ) {
    if( index>=nfi.size() || index>=nfj.size() ) {
      std::vector< Node > ant;
      //we have a conflict : because the lengths are equal, the remainder needs to be empty, which will lead to a conflict
      Node lni = getLength( ni );
      Node lnj = getLength( nj );
      ant.push_back( lni.eqNode( lnj ) );
      ant.push_back( getLengthTerm( ni ).eqNode( d_normal_forms_base[ni] ) );
      ant.push_back( getLengthTerm( nj ).eqNode( d_normal_forms_base[nj] ) );
      ant.insert( ant.end(), d_normal_forms_exp[ni].begin(), d_normal_forms_exp[ni].end() );
      ant.insert( ant.end(), d_normal_forms_exp[nj].begin(), d_normal_forms_exp[nj].end() );
      std::vector< Node > cc;
      std::vector< Node >& nfk = index>=nfi.size() ? nfj : nfi;
      for( unsigned index_k=index; index_k<nfk.size(); index_k++ ){
        cc.push_back( nfk[index_k].eqNode( d_emptyString ) );
      }
      Node conc = cc.size()==1 ? cc[0] : NodeManager::currentNM()->mkNode( kind::AND, cc );
      conc = Rewriter::rewrite( conc );
      sendLemma(mkExplain( ant ), conc, "Disequality Normalize Empty");
      //sendInfer(mkAnd( ant ), conc, "Disequality Normalize Empty");
      return -1;
    } else {
      Node i = nfi[index];
      Node j = nfj[index];
      Trace("strings-solve-debug")  << "...Processing(QED) " << i << " " << j << std::endl;
      if( !areEqual( i, j ) ) {
        if( i.getKind()==kind::CONST_STRING && j.getKind()==kind::CONST_STRING ) {
          unsigned int len_short = i.getConst<String>().size() < j.getConst<String>().size() ? i.getConst<String>().size() : j.getConst<String>().size();
          bool isSameFix = isRev ? i.getConst<String>().rstrncmp(j.getConst<String>(), len_short): i.getConst<String>().strncmp(j.getConst<String>(), len_short);
          if( isSameFix ) {
            //same prefix/suffix
            //k is the index of the string that is shorter
            Node nk = i.getConst<String>().size() < j.getConst<String>().size() ? i : j;
            Node nl = i.getConst<String>().size() < j.getConst<String>().size() ? j : i;
            Node remainderStr;
            if(isRev) {
              int new_len = nl.getConst<String>().size() - len_short;
              remainderStr = NodeManager::currentNM()->mkConst( nl.getConst<String>().substr(0, new_len) );
              Trace("strings-solve-debug-test") << "Rev. Break normal form of " << nl << " into " << nk << ", " << remainderStr << std::endl;
            } else {
              remainderStr = NodeManager::currentNM()->mkConst( j.getConst<String>().substr(len_short) );
              Trace("strings-solve-debug-test") << "Break normal form of " << nl << " into " << nk << ", " << remainderStr << std::endl;
            }
            if( i.getConst<String>().size() < j.getConst<String>().size() ) {
              nfj.insert( nfj.begin() + index + 1, remainderStr );
              nfj[index] = nfi[index];
            } else {
              nfi.insert( nfi.begin() + index + 1, remainderStr );
              nfi[index] = nfj[index];
            }
          } else {
            return 1;
          }
        } else {
          Node li = getLength( i );
          Node lj = getLength( j );
          if( areEqual( li, lj ) && areDisequal( i, j ) ) {
            Trace("strings-solve") << "Simple Case 2 : found equal length disequal sub strings " << i << " " << j << std::endl;
            //we are done: D-Remove
            return 1;
          } else {
            return 0;
          }
        }
      }
      index++;
    }
  }
  return 0;
}

void TheoryStrings::addNormalFormPair( Node n1, Node n2 ) {
  if( !isNormalFormPair( n1, n2 ) ){
    //Assert( !isNormalFormPair( n1, n2 ) );
    NodeList* lst;
    NodeListMap::iterator nf_i = d_nf_pairs.find( n1 );
    if( nf_i == d_nf_pairs.end() ){
      if( d_nf_pairs.find( n2 )!=d_nf_pairs.end() ){
        addNormalFormPair( n2, n1 );
        return;
      }
      lst = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                           ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
      d_nf_pairs.insertDataFromContextMemory( n1, lst );
      Trace("strings-nf") << "Create cache for " << n1 << std::endl;
    } else {
      lst = (*nf_i).second;
    }
    Trace("strings-nf") << "Add normal form pair : " << n1 << " " << n2 << std::endl;
    lst->push_back( n2 );
    Assert( isNormalFormPair( n1, n2 ) );
  } else {
    Trace("strings-nf-debug") << "Already a normal form pair " << n1 << " " << n2 << std::endl;
  }
}
bool TheoryStrings::isNormalFormPair( Node n1, Node n2 ) {
  //TODO: modulo equality?
  return isNormalFormPair2( n1, n2 ) || isNormalFormPair2( n2, n1 );
}
bool TheoryStrings::isNormalFormPair2( Node n1, Node n2 ) {
    //Trace("strings-debug") << "is normal form pair. " << n1 << " " << n2 << std::endl;
  NodeList* lst;
  NodeListMap::iterator nf_i = d_nf_pairs.find( n1 );
  if( nf_i != d_nf_pairs.end() ) {
    lst = (*nf_i).second;
    for( NodeList::const_iterator i = lst->begin(); i != lst->end(); ++i ) {
      Node n = *i;
      if( n==n2 ) {
          return true;
      }
    }
  }
  return false;
}

bool TheoryStrings::registerTerm( Node n ) {
  if(d_registered_terms_cache.find(n) == d_registered_terms_cache.end()) {
    Debug("strings-register") << "TheoryStrings::registerTerm() " << n << endl;
    if(n.getType().isString()) {
      if(n.getKind() == kind::STRING_SUBSTR_TOTAL) {
        Node lenxgti = NodeManager::currentNM()->mkNode( kind::GEQ,
                  NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n[0] ),
                  NodeManager::currentNM()->mkNode( kind::PLUS, n[1], n[2] ) );
        Node t1geq0 = NodeManager::currentNM()->mkNode(kind::GEQ, n[1], d_zero);
        Node t2geq0 = NodeManager::currentNM()->mkNode(kind::GT, n[2], d_zero);
        Node cond = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, lenxgti, t1geq0, t2geq0 ));
        Node sk1 = mkSkolemS( "ss1", 2 );
        Node sk3 = mkSkolemS( "ss3", 2 );
        Node x_eq_123 = n[0].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, sk1, n, sk3 ) );
        Node len_sk1_eq_i = n[1].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk1 ) );
        Node lenc = n[2].eqNode( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n ) );
        Node lemma = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::ITE, cond,
          NodeManager::currentNM()->mkNode( kind::AND, x_eq_123, len_sk1_eq_i, lenc ),
          n.eqNode(d_emptyString)));
        Trace("strings-lemma") << "Strings::Lemma SUBSTR : " << lemma << std::endl;
         Trace("strings-assert") << "(assert " << lemma << ")" << std::endl;
        d_out->lemma(lemma);
      }
      if( n.getKind()!=kind::STRING_CONCAT && n.getKind()!=kind::CONST_STRING ) {
        if( d_length_intro_vars.find(n)==d_length_intro_vars.end() ) {
          sendLengthLemma( n );
          ++(d_statistics.d_splits);
        }
      } else {
        Node sk = mkSkolemS("lsym", 2);
        StringsProxyVarAttribute spva;
        sk.setAttribute(spva,true);
        Node eq = Rewriter::rewrite( sk.eqNode(n) );
        Trace("strings-lemma") << "Strings::Lemma LENGTH Term : " << eq << std::endl;
        d_proxy_var[n] = sk;
        Trace("strings-assert") << "(assert " << eq << ")" << std::endl;
        d_out->lemma(eq);
        Node skl = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, sk );
        Node lsum;
        if( n.getKind() == kind::STRING_CONCAT ) {
          std::vector<Node> node_vec;
          for( unsigned i=0; i<n.getNumChildren(); i++ ) {
            Node lni = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n[i] );
            node_vec.push_back(lni);
          }
          lsum = NodeManager::currentNM()->mkNode( kind::PLUS, node_vec );
        } else if( n.getKind() == kind::CONST_STRING ) {
          lsum = NodeManager::currentNM()->mkConst( ::CVC4::Rational( n.getConst<String>().size() ) );
        }
        Node ceq = Rewriter::rewrite( skl.eqNode( lsum ) );
        Trace("strings-lemma") << "Strings::Lemma LENGTH : " << ceq << std::endl;
        Trace("strings-lemma-debug") << "  prerewrite : " << skl.eqNode( lsum ) << std::endl;
        Trace("strings-assert") << "(assert " << ceq << ")" << std::endl;
        d_out->lemma(ceq);
        //also add this to the equality engine
        if( n.getKind() == kind::CONST_STRING ) {
          d_equalityEngine.assertEquality( ceq, true, d_true );
        }
      }
      d_registered_terms_cache.insert(n);
      return true;
    } else {
      AlwaysAssert(false, "String Terms only in registerTerm.");
    }
  }
  return false;
}

void TheoryStrings::sendLemma( Node ant, Node conc, const char * c ) {
  if( conc.isNull() || conc == d_false ) {
    d_out->conflict(ant);
    Trace("strings-conflict") << "Strings::Conflict : " << c << " : " << ant << std::endl;
    Trace("strings-lemma") << "Strings::Conflict : " << c << " : " << ant << std::endl;
    Trace("strings-assert") << "(assert (not " << ant << ")) ; conflict " << c << std::endl;
    d_conflict = true;
  } else {
    Node lem;
    if( ant == d_true ) {
      lem = conc;
    }else{
      lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, ant, conc );
    }
    Trace("strings-lemma") << "Strings::Lemma " << c << " : " << lem << std::endl;
    Trace("strings-assert") << "(assert " << lem << ") ; lemma " << c << std::endl;
    d_lemma_cache.push_back( lem );
  }
}

void TheoryStrings::sendInfer( Node eq_exp, Node eq, const char * c ) {
  eq = Rewriter::rewrite( eq );
  if( eq==d_false || eq.getKind()==kind::OR ) {
    sendLemma( eq_exp, eq, c );
  } else {
    if( options::stringInferSym() ){
      std::vector< Node > vars;
      std::vector< Node > subs;
      std::vector< Node > unproc;
      inferSubstitutionProxyVars( eq_exp, vars, subs, unproc );
      if( unproc.empty() ){
        Trace("strings-lemma-debug") << "Strings::Infer " << eq << " from " << eq_exp << " by " << c << std::endl;
        Node eqs = eq.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
        Trace("strings-lemma-debug") << "Strings::Infer Alternate : " << eqs << std::endl;
        for( unsigned i=0; i<vars.size(); i++ ){
          Trace("strings-lemma-debug") << "  " << vars[i] << " -> " << subs[i] << std::endl;
        }
        sendLemma( d_true, eqs, c );
        return;
      }else{
        for( unsigned i=0; i<unproc.size(); i++ ){
          Trace("strings-lemma-debug") << "  non-trivial exp : " << unproc[i] << std::endl;
        }
      }
    }
    Trace("strings-lemma") << "Strings::Infer " << eq << " from " << eq_exp << " by " << c << std::endl;
    Trace("strings-assert") << "(assert (=> " << eq_exp << " " << eq << ")) ; infer " << c << std::endl;
    d_pending.push_back( eq );
    d_pending_exp[eq] = eq_exp;
    d_infer.push_back(eq);
    d_infer_exp.push_back(eq_exp);
  }
}

void TheoryStrings::sendSplit( Node a, Node b, const char * c, bool preq ) {
  Node eq = a.eqNode( b );
  eq = Rewriter::rewrite( eq );
  Node neq = NodeManager::currentNM()->mkNode( kind::NOT, eq );
  Node lemma_or = NodeManager::currentNM()->mkNode( kind::OR, eq, neq );
  Trace("strings-lemma") << "Strings::Lemma " << c << " SPLIT : " << lemma_or << std::endl;
  d_lemma_cache.push_back(lemma_or);
  d_pending_req_phase[eq] = preq;
  ++(d_statistics.d_splits);
}


void TheoryStrings::sendLengthLemma( Node n ){
  Node n_len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, n);
  if( options::stringSplitEmp() || !options::stringLenGeqZ() ){
    Node n_len_eq_z = n_len.eqNode( d_zero );
    //registerTerm( d_emptyString );
    Node n_len_eq_z_2 = n.eqNode( d_emptyString );
    n_len_eq_z = Rewriter::rewrite( n_len_eq_z );
    n_len_eq_z_2 = Rewriter::rewrite( n_len_eq_z_2 );
    Node n_len_geq_zero = NodeManager::currentNM()->mkNode( kind::OR, NodeManager::currentNM()->mkNode( kind::AND, n_len_eq_z, n_len_eq_z_2 ),
                NodeManager::currentNM()->mkNode( kind::GT, n_len, d_zero) );
    Trace("strings-lemma") << "Strings::Lemma LENGTH >= 0 : " << n_len_geq_zero << std::endl;
    d_out->lemma(n_len_geq_zero);
    d_out->requirePhase( n_len_eq_z, true );
    d_out->requirePhase( n_len_eq_z_2, true );
  }
  //AJR: probably a good idea
  if( options::stringLenGeqZ() ){
    Node n_len_geq = NodeManager::currentNM()->mkNode( kind::GEQ, n_len, d_zero);
    n_len_geq = Rewriter::rewrite( n_len_geq );
    d_out->lemma( n_len_geq );
  }
}

void TheoryStrings::inferSubstitutionProxyVars( Node n, std::vector< Node >& vars, std::vector< Node >& subs, std::vector< Node >& unproc ) {
  if( n.getKind()==kind::AND ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      inferSubstitutionProxyVars( n[i], vars, subs, unproc );
    }
    return;
  }else if( n.getKind()==kind::EQUAL ){
    Node ns = n.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    ns = Rewriter::rewrite( ns );
    if( ns.getKind()==kind::EQUAL ){
      Node s;
      Node v;
      for( unsigned i=0; i<2; i++ ){
        Node ss;
        if( ns[i].getAttribute(StringsProxyVarAttribute()) ){
          ss = ns[i];
        }else{
          NodeNodeMap::const_iterator it = d_proxy_var.find( ns[i] );
          if( it!=d_proxy_var.end() ){
            ss = (*it).second;
          }
        }
        if( !ss.isNull() ){
          v = ns[1-i];
          if( v.getNumChildren()==0 ){
            if( s.isNull() ){
              s = ss;
            }else{
              //both sides involved in proxy var
              if( ss==s ){
                return;
              }else{
                s = Node::null();
              }
            }
          }
        }
      }
      if( !s.isNull() ){
        subs.push_back( s );
        vars.push_back( v );
        return;
      }
    }else{
      n = ns;
    }
  }
  if( n!=d_true ){
    unproc.push_back( n );
  }
}


Node TheoryStrings::mkConcat( Node n1, Node n2 ) {
  return Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, n1, n2 ) );
}

Node TheoryStrings::mkConcat( Node n1, Node n2, Node n3 ) {
  return Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, n1, n2, n3 ) );
}

Node TheoryStrings::mkConcat( const std::vector< Node >& c ) {
  return Rewriter::rewrite( c.size()>1 ? NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, c ) : ( c.size()==1 ? c[0] : d_emptyString ) );
}

//isLenSplit: 0-yes, 1-no, 2-ignore
Node TheoryStrings::mkSkolemS( const char *c, int isLenSplit ) {
  Node n = NodeManager::currentNM()->mkSkolem( c, NodeManager::currentNM()->stringType(), "string sko" );
  d_length_intro_vars.insert(n);
  ++(d_statistics.d_new_skolems);
  if(isLenSplit == 0) {
    sendLengthLemma( n );
    ++(d_statistics.d_splits);
  } else if(isLenSplit == 1) {
    d_equalityEngine.assertEquality(n.eqNode(d_emptyString), false, d_true);
    Node len_n_gt_z = NodeManager::currentNM()->mkNode(kind::GT,
                        NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, n), d_zero);
    Trace("strings-lemma") << "Strings::Lemma SK-NON-ZERO : " << len_n_gt_z << std::endl;
    Trace("strings-assert") << "(assert " << len_n_gt_z << ")" << std::endl;
    d_out->lemma(len_n_gt_z);
  }
  return n;
}

Node TheoryStrings::mkExplain( std::vector< Node >& a ) {
  std::vector< Node > an;
  return mkExplain( a, an );
}

Node TheoryStrings::mkExplain( std::vector< Node >& a, std::vector< Node >& an ) {
  std::vector< TNode > antec_exp;
  for( unsigned i=0; i<a.size(); i++ ) {
    if( std::find( a.begin(), a.begin() + i, a[i] )==a.begin() + i ) {
      bool exp = true;
      Debug("strings-explain") << "Ask for explanation of " << a[i] << std::endl;
      //assert
      if(a[i].getKind() == kind::EQUAL) {
        //assert( hasTerm(a[i][0]) );
        //assert( hasTerm(a[i][1]) );
        Assert( areEqual(a[i][0], a[i][1]) );
        if( a[i][0]==a[i][1] ){
          exp = false;
        }
      } else if( a[i].getKind()==kind::NOT && a[i][0].getKind()==kind::EQUAL ) {
        Assert( hasTerm(a[i][0][0]) );
        Assert( hasTerm(a[i][0][1]) );
        AlwaysAssert( d_equalityEngine.areDisequal(a[i][0][0], a[i][0][1], true) );
      }else if( a[i].getKind() == kind::AND ){
        for( unsigned j=0; j<a[i].getNumChildren(); j++ ){
          a.push_back( a[i][j] );
        }
        exp = false;
      }
      if( exp ) {
        unsigned ps = antec_exp.size();
        explain(a[i], antec_exp);
        Debug("strings-explain") << "Done, explanation was : " << std::endl;
        for( unsigned j=ps; j<antec_exp.size(); j++ ) {
          Debug("strings-explain") << "  " << antec_exp[j] << std::endl;
        }
        Debug("strings-explain") << std::endl;
      }
    }
  }
  for( unsigned i=0; i<an.size(); i++ ) {
    if( std::find( an.begin(), an.begin() + i, an[i] )==an.begin() + i ){
      Debug("strings-explain") << "Add to explanation (new literal) " << an[i] << std::endl;
      antec_exp.push_back(an[i]);
    }
  }
  Node ant;
  if( antec_exp.empty() ) {
    ant = d_true;
  } else if( antec_exp.size()==1 ) {
    ant = antec_exp[0];
  } else {
    ant = NodeManager::currentNM()->mkNode( kind::AND, antec_exp );
  }
  ant = Rewriter::rewrite( ant );
  return ant;
}

Node TheoryStrings::mkAnd( std::vector< Node >& a ) {
  std::vector< Node > au;
  for( unsigned i=0; i<a.size(); i++ ){
    if( std::find( au.begin(), au.end(), a[i] )==au.end() ){
      au.push_back( a[i] );
    }
  }
  if( au.empty() ) {
    return d_true;
  } else if( au.size() == 1 ) {
    return au[0];
  } else {
    return NodeManager::currentNM()->mkNode( kind::AND, au );
  }
}

void TheoryStrings::getConcatVec( Node n, std::vector< Node >& c ) {
  if( n.getKind()==kind::STRING_CONCAT ) {
    for( unsigned i=0; i<n.getNumChildren(); i++ ) {
      if( !areEqual( n[i], d_emptyString ) ) {
        c.push_back( n[i] );
      }
    }
  } else {
    c.push_back( n );
  }
}

void TheoryStrings::debugPrintFlatForms( const char * tc ){
  for( unsigned k=0; k<d_eqcs.size(); k++ ){
    Node eqc = d_eqcs[k];
    Trace( tc ) << "EQC [" << eqc << "]" << std::endl;
    std::map< Node, Node >::iterator itc = d_eqc_to_const.find( eqc );
    if( itc!=d_eqc_to_const.end() ){
      Trace( tc ) << "  C: " << itc->second << std::endl;
    }
    for( unsigned i=0; i<d_eqc[eqc].size(); i++ ){
      Node n = d_eqc[eqc][i];
      Trace( tc ) << "    ";
      for( unsigned j=0; j<d_flat_form[n].size(); j++ ){
        Node fc = d_flat_form[n][j];
        itc = d_eqc_to_const.find( fc );
        Trace( tc ) << " ";
        if( itc!=d_eqc_to_const.end() ){
          Trace( tc ) << itc->second;
        }else{
          Trace( tc ) << fc;
        }
      }
      if( n!=eqc ){
        Trace( tc ) << ", from " << n;
      }
      Trace( tc ) << std::endl;
    }
  }
  Trace( tc ) << std::endl;
}

void TheoryStrings::checkNormalForms() {

  //first check for cycles, while building ordering of equivalence classes
  d_eqc.clear();
  d_flat_form.clear();
  Trace("strings-process") << "Check equivalence classes cycles...." << std::endl;
  d_eqcs.clear();
  for( unsigned i=0; i<d_strings_eqc.size(); i++ ){
    std::vector< Node > curr;
    std::vector< Node > exp;
    checkCycles( d_strings_eqc[i], curr, exp );
    if( hasProcessed() ){
      return;
    }
  }
  Trace("strings-process-debug") << "Done check cycles, lemmas = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << std::endl;

  if( !hasProcessed() ){
    //debug print flat forms
    if( Trace.isOn("strings-ff") ){
      Trace("strings-ff") << "Flat forms : " << std::endl;
      debugPrintFlatForms( "strings-ff" );
    }

    //inferences without recursively expanding flat forms (TODO)
        /*
    for( unsigned k=0; k<d_eqcs.size(); k++ ){
      Node eqc = d_eqcs[k];
      Node c;
      std::map< Node, Node >::iterator itc = d_eqc_to_const.find( eqc );
      if( itc!=d_eqc_to_const.end() ){
        c = itc->second;
      }
      std::map< Node, std::vector< Node > >::iterator it = d_eqc.find( eqc );
      if( it!=d_eqc.end() && it->second.size()>1 ){
        for( unsigned r=0; r<2; r++ ){
          bool success;
          int count = 0;
          do{
            success = true;
            Node curr = d_flat_form[it->second[0]][count];
            Node lcurr = getLength( curr );
            for( unsigned i=1; i<it->second.size(); i++ ){
              Node cc = d_flat_form[it->second[i]][count];
              if( cc!=curr ){
                //constant conflict? TODO
                //if lengths are the same, apply LengthEq
                Node lcc = getLength( cc );
                if( areEqual( lcurr, lcc ) ){
                  std::vector< Node > exp;
                  Node a = it->second[0];
                  Node b = it->second[i];
                  addToExplanation( a, b, exp );
                  //explain why prefixes up to now were the same
                  for( unsigned j=0; j<count; j++ ){
                    addToExplanation( a[d_flat_form_index[a][j]], b[d_flat_form_index[b][j]], exp );
                  }
                  //explain why components are empty
                  //TODO
                  addToExplanation( lcurr, lcc, exp );
                  sendInfer( mkAnd( exp ), curr.eqNode( cc ), "F-LengthEq" );
                  return;
                }
                success = false;
              }
            }
            count++;
            //check if we are at the endpoint of any string
            for( unsigned i=0; i<it->second.size(); i++ ){
              if( count==d_flat_form[it->second[i]].size() ){
                Node a = it->second[i];
                for( unsigned j=0; j<it->second.size(); j++ ){
                  if( i!=j ){
                    //remainder must be empty
                    if( count<d_flat_form[it->second[j]].size() ){
                      Node b = it->second[j];
                      std::vector< Node > exp;
                      addToExplanation( a, b, exp );
                      for( unsigned j=0; j<count; j++ ){
                        addToExplanation( a[d_flat_form_index[a][j]], b[d_flat_form_index[b][j]], exp );
                      }
                      
                    }
                  }
                }
              }
            }
          }while( success &&  );
          
          if( r==1 ){
            for( unsigned i=0; i<it->second.size(); i++ ){
              std::reverse( d_flat_form[it->second].begin(), d_flat_form[it->second].end() );
              std::reverse( d_flat_form_index[it->second].begin(), d_flat_form_index[it->second].end() );
            }
          }
        }
      }
    }
        */
    if( !hasProcessed() ){
      //get equivalence classes
      //d_eqcs.clear();
      //getEquivalenceClasses( d_eqcs );
      Trace("strings-process") << "Normalize equivalence classes...." << std::endl;
      //calculate normal forms for each equivalence class, possibly adding splitting lemmas
      d_normal_forms.clear();
      d_normal_forms_exp.clear();
      std::map< Node, Node > nf_to_eqc;
      std::map< Node, Node > eqc_to_exp;
      for( unsigned i=0; i<d_eqcs.size(); i++ ) {
        Node eqc = d_eqcs[i];
        Trace("strings-process-debug") << "- Verify normal forms are the same for " << eqc << std::endl;
        std::vector< Node > visited;
        std::vector< Node > nf;
        std::vector< Node > nf_exp;
        normalizeEquivalenceClass(eqc, visited, nf, nf_exp);
        Trace("strings-debug") << "Finished normalizing eqc..." << std::endl;
        if( d_conflict ) {
          return;
        } else if ( d_pending.empty() && d_lemma_cache.empty() ) {
          Node nf_term = mkConcat( nf );
          if( nf_to_eqc.find( nf_term )!=nf_to_eqc.end() ) {
            //Trace("strings-debug") << "Merge because of normal form : " << eqc << " and " << nf_to_eqc[nf_term] << " both have normal form " << nf_term << std::endl;
            //two equivalence classes have same normal form, merge
            nf_exp.push_back( eqc_to_exp[nf_to_eqc[nf_term]] );
            Node eq = eqc.eqNode( nf_to_eqc[nf_term] );
            sendInfer( mkAnd( nf_exp ), eq, "Normal_Form" );
            //d_equalityEngine.assertEquality( eq, true, eq_exp );
          } else {
            nf_to_eqc[nf_term] = eqc;
            eqc_to_exp[eqc] = mkAnd( nf_exp );
          }
        }
        Trace("strings-process-debug") << "Done verifying normal forms are the same for " << eqc << std::endl;
      }

      if(Debug.isOn("strings-nf")) {
        Debug("strings-nf") << "**** Normal forms are : " << std::endl;
        for( std::map< Node, Node >::iterator it = nf_to_eqc.begin(); it != nf_to_eqc.end(); ++it ){
          Debug("strings-nf") << "  normal_form(" << it->second << ") = " << it->first << std::endl;
        }
        Debug("strings-nf") << std::endl;
      }
      
      if( !hasProcessed() ){
        checkExtendedFuncsEval( 1 );
        Trace("strings-process-debug") << "Done check extended functions re-eval, addedFact = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
        if( !hasProcessed() ){
          //process disequalities between equivalence classes
          checkDeqNF();
          Trace("strings-process-debug") << "Done check disequalities, addedFact = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
        }
      }
    }
  }
  Trace("strings-solve") << "Finished check normal forms, #lemmas = " << d_lemma_cache.size() << ", conflict = " << d_conflict << std::endl;
}

Node TheoryStrings::checkCycles( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp ){
  if( std::find( curr.begin(), curr.end(), eqc )!=curr.end() ){
    // a loop
    return eqc;
  }else if( std::find( d_eqcs.begin(), d_eqcs.end(), eqc )==d_eqcs.end() ){
    curr.push_back( eqc );
    //look at all terms in this equivalence class
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ) {
      Node n = (*eqc_i);
      if( std::find( d_congruent.begin(), d_congruent.end(), n )==d_congruent.end() ){
        Trace("strings-cycle") << "Check term : " << n << std::endl;
        if( n.getKind() == kind::STRING_CONCAT ) {
          if( eqc!=d_emptyString_r ){
            d_eqc[eqc].push_back( n );
          }
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            Node nr = getRepresentative( n[i] );
            if( eqc==d_emptyString_r ){
              //for empty eqc, ensure all components are empty
              if( nr!=d_emptyString_r ){
                sendInfer( n.eqNode( d_emptyString ), n[i].eqNode( d_emptyString ), "I_CYCLE_E" );
                return Node::null();
              }
            }else{
              if( nr!=d_emptyString_r ){
                d_flat_form[n].push_back( nr );
                d_flat_form_index[n].push_back( i );
              }
              //for non-empty eqc, recurse and see if we find a loop
              Node ncy = checkCycles( nr, curr, exp );
              if( !ncy.isNull() ){
                if( ncy==eqc ){
                  //can infer all other components must be empty
                  for( unsigned j=0; j<n.getNumChildren(); j++ ){
                    //take first non-empty
                    if( j!=i && !areEqual( n[j], d_emptyString ) ){
                      sendInfer( mkAnd( exp ), n[j].eqNode( d_emptyString ), "I_CYCLE" );
                      return Node::null();
                    }
                  }
                  Trace("strings-error") << "Looping term should be congruent : " << n << " " << eqc << " " << ncy << std::endl;
                  //should find a non-empty component, otherwise would have been singular congruent (I_Norm_S)
                  Assert( false );
                }else{
                  if( n!=eqc ){
                    exp.push_back( n.eqNode( eqc ) );
                  }
                  if( nr!=n[i] ){
                    exp.push_back( nr.eqNode( n[i] ) );
                  }
                  return ncy;
                }
              }else{
                if( hasProcessed() ){
                  return Node::null();
                }
              }
            }
          }
        }
      }
      ++eqc_i;
    }
    curr.pop_back();
    //now we can add it to the list of equivalence classes
    d_eqcs.push_back( eqc );
  }else{
    //already processed
  }
  return Node::null();
}


void TheoryStrings::checkDeqNF() {
  if( !d_conflict && d_lemma_cache.empty() ){
    std::vector< Node > eqcs;
    getEquivalenceClasses( eqcs );
    std::vector< std::vector< Node > > cols;
    std::vector< Node > lts;
    separateByLength( eqcs, cols, lts );
    for( unsigned i=0; i<cols.size(); i++ ){
      if( cols[i].size()>1 && d_lemma_cache.empty() ){
      Trace("strings-solve") << "- Verify disequalities are processed for ";
      printConcat( d_normal_forms[cols[i][0]], "strings-solve" );
      Trace("strings-solve")  << "..." << std::endl;

      //must ensure that normal forms are disequal
      for( unsigned j=0; j<cols[i].size(); j++ ){
        for( unsigned k=(j+1); k<cols[i].size(); k++ ){
          if( areDisequal( cols[i][j], cols[i][k] ) ){
            Assert( !d_conflict );
            //if( !areDisequal( cols[i][j], cols[i][k] ) ){
            //  sendSplit( cols[i][j], cols[i][k], "D-NORM", true );
            //  return;
            //}else{
              Trace("strings-solve") << "- Compare ";
              printConcat( d_normal_forms[cols[i][j]], "strings-solve" );
              Trace("strings-solve") << " against ";
              printConcat( d_normal_forms[cols[i][k]], "strings-solve" );
              Trace("strings-solve")  << "..." << std::endl;
              if( processDeq( cols[i][j], cols[i][k] ) ){
                return;
              }
            //}
          }
        }
      }
    }
   }
  }
}

void TheoryStrings::checkLengthsEqc() {
  if( options::stringLenNorm() ){
    std::vector< Node > nodes;
    getEquivalenceClasses( nodes );
    for( unsigned i=0; i<nodes.size(); i++ ){
      if( d_normal_forms[nodes[i]].size()>1 ) {
        Trace("strings-process-debug") << "Process length constraints for " << nodes[i] << std::endl;
        //check if there is a length term for this equivalence class
        EqcInfo* ei = getOrMakeEqcInfo( nodes[i], false );
        Node lt = ei ? ei->d_length_term : Node::null();
        if( !lt.isNull() ) {
          Node llt = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, lt );
          //now, check if length normalization has occurred
          if( ei->d_normalized_length.get().isNull() ) {
            //if not, add the lemma
            std::vector< Node > ant;
            ant.insert( ant.end(), d_normal_forms_exp[nodes[i]].begin(), d_normal_forms_exp[nodes[i]].end() );
            ant.push_back( d_normal_forms_base[nodes[i]].eqNode( lt ) );
            Node lc = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, mkConcat( d_normal_forms[nodes[i]] ) );
            lc = Rewriter::rewrite( lc );
            Node eq = llt.eqNode( lc );
            ei->d_normalized_length.set( eq );
            sendLemma( mkExplain( ant ), eq, "LEN-NORM" );
          }
        }
      } else {
        Trace("strings-process-debug") << "Do not process length constraints for " << nodes[i] << " " << d_normal_forms[nodes[i]].size() << std::endl;
      }
    }
  }
}

void TheoryStrings::checkCardinality() {
  //int cardinality = options::stringCharCardinality();
  //Trace("strings-solve-debug2") << "get cardinality: " << cardinality << endl;

  std::vector< Node > eqcs;
  getEquivalenceClasses( eqcs );

  std::vector< std::vector< Node > > cols;
  std::vector< Node > lts;
  separateByLength( eqcs, cols, lts );

  for( unsigned i = 0; i<cols.size(); ++i ) {
    Node lr = lts[i];
    Trace("strings-card") << "Number of strings with length equal to " << lr << " is " << cols[i].size() << std::endl;
    if( cols[i].size() > 1 ) {
      // size > c^k
      unsigned card_need = 1;
      double curr = (double)cols[i].size()-1;
      while( curr>d_card_size ){
        curr = curr/(double)d_card_size;
        card_need++;
      }
      Node cmp = NodeManager::currentNM()->mkNode( kind::GEQ, lr, NodeManager::currentNM()->mkConst( Rational( card_need ) ) );
      cmp = Rewriter::rewrite( cmp );
      if( cmp!=d_true ){
        unsigned int int_k = (unsigned int)card_need;
        bool allDisequal = true;
        for( std::vector< Node >::iterator itr1 = cols[i].begin();
            itr1 != cols[i].end(); ++itr1) {
          for( std::vector< Node >::iterator itr2 = itr1 + 1;
            itr2 != cols[i].end(); ++itr2) {
            if(!areDisequal( *itr1, *itr2 )) {
              allDisequal = false;
              // add split lemma
              sendSplit( *itr1, *itr2, "CARD-SP" );
              return;
            }
          }
        }
        if( allDisequal ){
          EqcInfo* ei = getOrMakeEqcInfo( lr, true );
          Trace("strings-card") << "Previous cardinality used for " << lr << " is " << ((int)ei->d_cardinality_lem_k.get()-1) << std::endl;
          if( int_k+1 > ei->d_cardinality_lem_k.get() ){
            Node k_node = NodeManager::currentNM()->mkConst( ::CVC4::Rational( int_k ) );
            //add cardinality lemma
            Node dist = NodeManager::currentNM()->mkNode( kind::DISTINCT, cols[i] );
            std::vector< Node > vec_node;
            vec_node.push_back( dist );
            for( std::vector< Node >::iterator itr1 = cols[i].begin();
                itr1 != cols[i].end(); ++itr1) {
              Node len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, *itr1 );
              if( len!=lr ) {
                Node len_eq_lr = len.eqNode(lr);
                vec_node.push_back( len_eq_lr );
              }
            }
            Node antc = NodeManager::currentNM()->mkNode( kind::AND, vec_node );
            Node len = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, cols[i][0] );
            Node cons = NodeManager::currentNM()->mkNode( kind::GEQ, len, k_node );
            cons = Rewriter::rewrite( cons );
            ei->d_cardinality_lem_k.set( int_k+1 );
            if( cons!=d_true ){
              sendLemma( antc, cons, "CARDINALITY" );
              return;
            }
          }
        }
      }
    }
  }
}

void TheoryStrings::getEquivalenceClasses( std::vector< Node >& eqcs ) {
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ) {
    Node eqc = (*eqcs_i);
    //if eqc.getType is string
    if (eqc.getType().isString()) {
      eqcs.push_back( eqc );
    }
    ++eqcs_i;
  }
}

void TheoryStrings::getFinalNormalForm( Node n, std::vector< Node >& nf, std::vector< Node >& exp ) {
  if( n!=d_emptyString ) {
    if( n.getKind()==kind::STRING_CONCAT ) {
      for( unsigned i=0; i<n.getNumChildren(); i++ ) {
        getFinalNormalForm( n[i], nf, exp );
      }
    } else {
      Trace("strings-debug") << "Get final normal form " << n << std::endl;
      Assert( d_equalityEngine.hasTerm( n ) );
      Node nr = d_equalityEngine.getRepresentative( n );
      EqcInfo *eqc_n = getOrMakeEqcInfo( nr, false );
      Node nc = eqc_n ? eqc_n->d_const_term.get() : Node::null();
      if( !nc.isNull() ) {
        nf.push_back( nc );
        if( n!=nc ) {
          exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n, nc ) );
        }
      } else {
        Assert( d_normal_forms.find( nr )!=d_normal_forms.end() );
        if( d_normal_forms[nr][0]==nr ) {
          Assert( d_normal_forms[nr].size()==1 );
          nf.push_back( nr );
          if( n!=nr ) {
            exp.push_back( NodeManager::currentNM()->mkNode( kind::EQUAL, n, nr ) );
          }
        } else {
          for( unsigned i=0; i<d_normal_forms[nr].size(); i++ ) {
            Assert( d_normal_forms[nr][i]!=nr );
            getFinalNormalForm( d_normal_forms[nr][i], nf, exp );
          }
          exp.insert( exp.end(), d_normal_forms_exp[nr].begin(), d_normal_forms_exp[nr].end() );
        }
      }
      Trace("strings-ind-nf") << "The final normal form of " << n << " is " << nf << std::endl;
    }
  }
}

void TheoryStrings::separateByLength(std::vector< Node >& n,
  std::vector< std::vector< Node > >& cols,
  std::vector< Node >& lts ) {
  unsigned leqc_counter = 0;
  std::map< Node, unsigned > eqc_to_leqc;
  std::map< unsigned, Node > leqc_to_eqc;
  std::map< unsigned, std::vector< Node > > eqc_to_strings;
  for( unsigned i=0; i<n.size(); i++ ) {
    Node eqc = n[i];
    Assert( d_equalityEngine.getRepresentative(eqc)==eqc );
    EqcInfo* ei = getOrMakeEqcInfo( eqc, false );
    Node lt = ei ? ei->d_length_term : Node::null();
    if( !lt.isNull() ){
      lt = NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, lt );
      Node r = d_equalityEngine.getRepresentative( lt );
      if( eqc_to_leqc.find( r )==eqc_to_leqc.end() ){
      eqc_to_leqc[r] = leqc_counter;
      leqc_to_eqc[leqc_counter] = r;
      leqc_counter++;
      }
      eqc_to_strings[ eqc_to_leqc[r] ].push_back( eqc );
    }else{
      eqc_to_strings[leqc_counter].push_back( eqc );
      leqc_counter++;
    }
  }
  for( std::map< unsigned, std::vector< Node > >::iterator it = eqc_to_strings.begin(); it != eqc_to_strings.end(); ++it ){
    std::vector< Node > vec;
    vec.insert( vec.end(), it->second.begin(), it->second.end() );
    lts.push_back( leqc_to_eqc[it->first] );
    cols.push_back( vec );
  }
}

void TheoryStrings::printConcat( std::vector< Node >& n, const char * c ) {
  for( unsigned i=0; i<n.size(); i++ ){
    if( i>0 ) Trace(c) << " ++ ";
    Trace(c) << n[i];
  }
}


//// Measurements
/*
void TheoryStrings::updateMpl( Node n, int b ) {
  if(d_mpl.find(n) == d_mpl.end()) {
    //d_curr_cardinality.get();
    d_mpl[n] = b;
  } else if(b < d_mpl[n]) {
    d_mpl[n] = b;
  }
}
*/

//// Regular Expressions
Node TheoryStrings::mkRegExpAntec(Node atom, Node ant) {
  if(d_regexp_ant.find(atom) == d_regexp_ant.end()) {
    return Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::AND, ant, atom) );
  } else {
    Node n = d_regexp_ant[atom];
    return Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::AND, ant, n) );
  }
}

Node TheoryStrings::normalizeRegexp(Node r) {
  Node nf_r = r;
  if(d_nf_regexps.find(r) != d_nf_regexps.end()) {
    nf_r = d_nf_regexps[r];
  } else {
    std::vector< Node > nf_exp;
    if(!d_regexp_opr.checkConstRegExp(r)) {
      switch( r.getKind() ) {
        case kind::REGEXP_EMPTY:
        case kind::REGEXP_SIGMA: {
          break;
        }
        case kind::STRING_TO_REGEXP: {
          if(r[0].isConst()) {
            break;
          } else {
            if(d_normal_forms.find( r[0] ) != d_normal_forms.end()) {
              nf_r = mkConcat( d_normal_forms[r[0]] );
              Debug("regexp-nf") << "Term: " << r[0] << " has a normal form " << nf_r << std::endl;
              nf_exp.insert(nf_exp.end(), d_normal_forms_exp[r[0]].begin(), d_normal_forms_exp[r[0]].end());
              nf_r = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, nf_r) );
            }
          }
        }
        case kind::REGEXP_CONCAT:
        case kind::REGEXP_UNION:
        case kind::REGEXP_INTER: {
          bool flag = false;
          std::vector< Node > vec_nodes;
          for(unsigned i=0; i<r.getNumChildren(); ++i) {
            Node rtmp = normalizeRegexp(r[i]);
            vec_nodes.push_back(rtmp);
            if(rtmp != r[i]) {
              flag = true;
            }
          }
          if(flag) {
            Node rtmp = vec_nodes.size()==1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode(r.getKind(), vec_nodes);
            nf_r = Rewriter::rewrite( rtmp );
          }
        }
        case kind::REGEXP_STAR: {
          Node rtmp = normalizeRegexp(r[0]);
          if(rtmp != r[0]) {
            rtmp = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, rtmp);
            nf_r = Rewriter::rewrite( rtmp );
          }
        }
        default: {
          Unreachable();
        }
      }
    }
    d_nf_regexps[r] = nf_r;
    d_nf_regexps_exp[r] = nf_exp;
  }
  return nf_r;
}

bool TheoryStrings::normalizePosMemberships(std::map< Node, std::vector< Node > > &memb_with_exps) {
  std::map< Node, std::vector< Node > > unprocessed_x_exps;
  std::map< Node, std::vector< Node > > unprocessed_memberships;
  std::map< Node, std::vector< Node > > unprocessed_memberships_bases;
  bool addLemma = false;

  Trace("regexp-check") << "Normalizing Positive Memberships ... " << std::endl;

  for(NodeListMap::const_iterator itr_xr = d_pos_memberships.begin();
    itr_xr != d_pos_memberships.end(); ++itr_xr ) {
    Node x = (*itr_xr).first;
    NodeList* lst = (*itr_xr).second;
    Node nf_x = x;
    std::vector< Node > nf_x_exp;
    if(d_normal_forms.find( x ) != d_normal_forms.end()) {
      //nf_x = mkConcat( d_normal_forms[x] );
      nf_x_exp.insert(nf_x_exp.end(), d_normal_forms_exp[x].begin(), d_normal_forms_exp[x].end());
      //Debug("regexp-nf") << "Term: " << x << " has a normal form " << ret << std::endl;
    } else {
      Assert(false);
    }
    Trace("regexp-nf") << "Checking Memberships for N(" << x << ") = " << nf_x << " :" << std::endl;

    std::vector< Node > vec_x;
    std::vector< Node > vec_r;
    for(NodeList::const_iterator itr_lst = lst->begin();
        itr_lst != lst->end(); ++itr_lst) {
      Node r = *itr_lst;
      Node nf_r = normalizeRegexp((*lst)[0]);
      Node memb = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, nf_x, nf_r);
      if(d_processed_memberships.find(memb) == d_processed_memberships.end()) {
        if(d_regexp_opr.checkConstRegExp(nf_r)) {
          vec_x.push_back(x);
          vec_r.push_back(r);
        } else {
          Trace("regexp-nf") << "Handling Symbolic Regexp for N(" << r << ") = " << nf_r << std::endl;
          //TODO: handle symbolic ones
          addLemma = true;
        }
        d_processed_memberships.insert(memb);
      }
    }
    if(!vec_x.empty()) {
      if(unprocessed_x_exps.find(nf_x) == unprocessed_x_exps.end()) {
        unprocessed_x_exps[nf_x] = nf_x_exp;
        unprocessed_memberships[nf_x] = vec_r;
        unprocessed_memberships_bases[nf_x] = vec_x;
      } else {
        unprocessed_x_exps[nf_x].insert(unprocessed_x_exps[nf_x].end(), nf_x_exp.begin(), nf_x_exp.end());
        unprocessed_memberships[nf_x].insert(unprocessed_memberships[nf_x].end(), vec_r.begin(), vec_r.end());
        unprocessed_memberships_bases[nf_x].insert(unprocessed_memberships_bases[nf_x].end(), vec_x.begin(), vec_x.end());
      }
    }
  }
  //Intersection
  for(std::map< Node, std::vector< Node > >::const_iterator itr = unprocessed_memberships.begin();
      itr != unprocessed_memberships.end(); ++itr) {
    Node nf_x = itr->first;
    std::vector< Node > exp( unprocessed_x_exps[nf_x] );
    Node r = itr->second[0];
    //get nf_r
    Node inter_r = d_nf_regexps[r];
    exp.insert(exp.end(), d_nf_regexps_exp[r].begin(), d_nf_regexps_exp[r].end());
    Node x = unprocessed_memberships_bases[itr->first][0];
    Node memb = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, x, r);
    exp.push_back(memb);
    for(std::size_t i=1; i < itr->second.size(); i++) {
      //exps
      Node r2 = itr->second[i];
      Node inter_r2 = d_nf_regexps[r2];
      exp.insert(exp.end(), d_nf_regexps_exp[r2].begin(), d_nf_regexps_exp[r2].end());
      Node x2 = unprocessed_memberships_bases[itr->first][i];
      memb = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, x2, r2);
      exp.push_back(memb);
      //intersection
      bool spflag = false;
      inter_r = d_regexp_opr.intersect(inter_r, inter_r2, spflag);
      if(inter_r == d_emptyRegexp) {
        //conflict
        Node antec = exp.size() == 1? exp[0] : NodeManager::currentNM()->mkNode(kind::AND, exp);
        Node conc;
        sendLemma(antec, conc, "INTERSEC CONFLICT");
        addLemma = true;
        break;
      }
    }
    //infer
    if(!d_conflict) {
      memb = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, nf_x, inter_r) );
      memb_with_exps[memb] = exp;
    } else {
      break;
    }
  }

  return addLemma;
}

bool TheoryStrings::applyRConsume( CVC4::String &s, Node &r) {
  Trace("regexp-derivative") << "TheoryStrings::derivative: s=" << s << ", r= " << r << std::endl;
  Assert( d_regexp_opr.checkConstRegExp(r) );

  if( !s.isEmptyString() ) {
    Node dc = r;

    for(unsigned i=0; i<s.size(); ++i) {
      CVC4::String c = s.substr(i, 1);
      Node dc2;
      int rt = d_regexp_opr.derivativeS(dc, c, dc2);
      dc = dc2;
      if(rt == 0) {
        Unreachable();
      } else if(rt == 2) {
        return false;
      }
    }
    r = dc;
  }

  return true;
}

Node TheoryStrings::applyRSplit(Node s1, Node s2, Node r) {
  Assert(d_regexp_opr.checkConstRegExp(r));

  std::vector< std::pair< Node, Node > > vec_can;
  d_regexp_opr.splitRegExp(r, vec_can);
  //TODO: lazy cache or eager?
  std::vector< Node > vec_or;

  for(unsigned int i=0; i<vec_can.size(); i++) {
    Node m1 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s1, vec_can[i].first);
    Node m2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s2, vec_can[i].second);
    Node c = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::AND, m1, m2) );
    vec_or.push_back( c );
  }
  Node conc = vec_or.size()==0? Node::null() : vec_or.size()==1 ? vec_or[0] : Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::OR, vec_or) );
  return conc;
}

bool TheoryStrings::applyRLen(std::map< Node, std::vector< Node > > &XinR_with_exps) {
  if(XinR_with_exps.size() > 0) {
    //TODO: get vector, var, store.
    return true;
  } else  {
    return false;
  }
}

bool TheoryStrings::checkMembershipsWithoutLength(
  std::map< Node, std::vector< Node > > &memb_with_exps,
  std::map< Node, std::vector< Node > > &XinR_with_exps) {
  for(std::map< Node, std::vector< Node > >::const_iterator itr = memb_with_exps.begin();
      itr != memb_with_exps.end(); ++itr) {
    Node memb = itr->first;
    Node s = memb[0];
    Node r = memb[1];
    if(s.isConst()) {
      memb = Rewriter::rewrite( memb );
      if(memb == d_false) {
        Node antec = itr->second.size() == 1? itr->second[0] : NodeManager::currentNM()->mkNode(kind::AND, itr->second);
        Node conc;
        sendLemma(antec, conc, "MEMBERSHIP CONFLICT");
        //addLemma = true;
        return true;
      } else {
        Assert(memb == d_true);
      }
    } else if(s.getKind() == kind::VARIABLE) {
      //add to XinR
      XinR_with_exps[itr->first] = itr->second;
    } else {
      Assert(s.getKind() == kind::STRING_CONCAT);
      Node antec = itr->second.size() == 1? itr->second[0] : NodeManager::currentNM()->mkNode(kind::AND, itr->second);
      Node conc;
      for( unsigned i=0; i<s.getNumChildren(); i++ ) {
        if(s[i].isConst()) {
          CVC4::String str( s[0].getConst< String >() );
          //R-Consume, see Tianyi's thesis
          if(!applyRConsume(str, r)) {
            sendLemma(antec, conc, "R-Consume CONFLICT");
            //addLemma = true;
            return true;
          }
        } else {
          //R-Split, see Tianyi's thesis
          if(i == s.getNumChildren() - 1) {
            //add to XinR
            Node memb2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s[i], r);
            XinR_with_exps[itr->first] = itr->second;
          } else {
            Node s1 = s[i];
            std::vector< Node > vec_s2;
            for( unsigned j=i+1; j<s.getNumChildren(); j++ ) {
              vec_s2.push_back(s[j]);
            }
            Node s2 = mkConcat(vec_s2);
            conc = applyRSplit(s1, s2, r);
            if(conc == d_true) {
              break;
            } else if(conc.isNull() || conc == d_false) {
              conc = Node::null();
              sendLemma(antec, conc, "R-Split Conflict");
              //addLemma = true;
              return true;
            } else {
              sendLemma(antec, conc, "R-Split");
              //addLemma = true;
              return true;
            }
          }
        }
      }
    }
  }
  return false;
}

bool TheoryStrings::checkMemberships2() {
  bool addedLemma = false;
  d_nf_regexps.clear();
  d_nf_regexps_exp.clear();
  std::map< Node, std::vector< Node > > memb_with_exps;
  std::map< Node, std::vector< Node > > XinR_with_exps;

  addedLemma = normalizePosMemberships( memb_with_exps );
  if(!d_conflict) {
    // main procedure
    addedLemma |= checkMembershipsWithoutLength( memb_with_exps, XinR_with_exps );
    //TODO: check addlemma
    if (!addedLemma && !d_conflict) {
      for(std::map< Node, std::vector< Node > >::const_iterator itr = XinR_with_exps.begin();
          itr != XinR_with_exps.end(); ++itr) {
        std::vector<Node> vec_or;
        d_regexp_opr.disjunctRegExp( itr->first, vec_or );
        Node tmp = NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec_or);
        Trace("regexp-process") << "Got r: " << itr->first << " to " << tmp << std::endl;
        /*
        if(r.getKind() == kind::REGEXP_STAR) {
          //TODO: apply R-Len
          addedLemma = applyRLen(XinR_with_exps);
        } else {
          //TODO: split
        }
        */
      }
      Assert(false); //TODO:tmp
    }
  }

  return addedLemma;
}

void TheoryStrings::checkMemberships() {
  bool addedLemma = false;
  bool changed = false;
  std::vector< Node > processed;
  std::vector< Node > cprocessed;

  Trace("regexp-debug") << "Checking Memberships ... " << std::endl;
  //if(options::stringEIT()) {
    //TODO: Opt for normal forms
    for(NodeListMap::const_iterator itr_xr = d_pos_memberships.begin();
      itr_xr != d_pos_memberships.end(); ++itr_xr ) {
      bool spflag = false;
      Node x = (*itr_xr).first;
      NodeList* lst = (*itr_xr).second;
      Trace("regexp-debug") << "Checking Memberships for " << x << std::endl;
      if(d_inter_index.find(x) == d_inter_index.end()) {
        d_inter_index[x] = 0;
      }
      int cur_inter_idx = d_inter_index[x];
      if(cur_inter_idx != (int)lst->size()) {
        if(lst->size() == 1) {
          d_inter_cache[x] = (*lst)[0];
          d_inter_index[x] = 1;
          Trace("regexp-debug") << "... only one choice " << std::endl;
        } else if(lst->size() > 1) {
          Node r;
          if(d_inter_cache.find(x) != d_inter_cache.end()) {
            r = d_inter_cache[x];
          }
          if(r.isNull()) {
            r = (*lst)[0];
            cur_inter_idx = 1;
          }
          NodeList::const_iterator itr_lst = lst->begin();
          for(int i=0; i<cur_inter_idx; i++) {
            ++itr_lst;
          }
          Trace("regexp-debug") << "... staring from : " << cur_inter_idx << ", we have " << lst->size() << std::endl;
          for(;itr_lst != lst->end(); ++itr_lst) {
            Node r2 = *itr_lst;
            r = d_regexp_opr.intersect(r, r2, spflag);
            if(spflag) {
              break;
            } else if(r == d_emptyRegexp) {
              std::vector< Node > vec_nodes;
              ++itr_lst;
              for(NodeList::const_iterator itr2 = lst->begin();
                itr2 != itr_lst; ++itr2) {
                Node n = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, x, *itr2);
                vec_nodes.push_back( n );
              }
              Node antec = vec_nodes.size() == 1? vec_nodes[0] : NodeManager::currentNM()->mkNode(kind::AND, vec_nodes);
              Node conc;
              sendLemma(antec, conc, "INTERSEC CONFLICT");
              addedLemma = true;
              break;
            }
            if(d_conflict) {
              break;
            }
          }
          //updates
          if(!d_conflict && !spflag) {
            d_inter_cache[x] = r;
            d_inter_index[x] = (int)lst->size();
          }
        }
      }
    }
  //}

  Trace("regexp-debug") << "... No Intersec Conflict in Memberships, addedLemma: " << addedLemma << std::endl;
  if(!addedLemma) {
    for( unsigned i=0; i<d_regexp_memberships.size(); i++ ) {
      //check regular expression membership
      Node assertion = d_regexp_memberships[i];
      if( d_regexp_ucached.find(assertion) == d_regexp_ucached.end()
        && d_regexp_ccached.find(assertion) == d_regexp_ccached.end() ) {
        Trace("strings-regexp") << "We have regular expression assertion : " << assertion << std::endl;
        Node atom = assertion.getKind()==kind::NOT ? assertion[0] : assertion;
        bool polarity = assertion.getKind()!=kind::NOT;
        bool flag = true;
        Node x = atom[0];
        Node r = atom[1];
        std::vector< Node > rnfexp;

        if(options::stringOpt1()) {
          if(!x.isConst()) {
            x = getNormalString( x, rnfexp);
            changed = true;
          }
          if(!d_regexp_opr.checkConstRegExp(r)) {
            r = getNormalSymRegExp(r, rnfexp);
            changed = true;
          }
          Trace("strings-regexp-nf") << "Term " << atom << " is normalized to " << x << " IN " << r << std::endl;
          if(changed) {
            Node tmp = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, x, r) );
            if(!polarity) {
              tmp = tmp.negate();
            }
            if(tmp == d_true) {
              d_regexp_ccached.insert(assertion);
              continue;
            } else if(tmp == d_false) {
              Node antec = mkRegExpAntec(assertion, mkExplain(rnfexp));
              Node conc = Node::null();
              sendLemma(antec, conc, "REGEXP NF Conflict");
              addedLemma = true;
              break;
            }
          }
        }

        if( polarity ) {
          flag = checkPDerivative(x, r, atom, addedLemma, processed, cprocessed, rnfexp);
          if(options::stringOpt2() && flag) {
            if(d_regexp_opr.checkConstRegExp(r) && x.getKind()==kind::STRING_CONCAT) {
              std::vector< std::pair< Node, Node > > vec_can;
              d_regexp_opr.splitRegExp(r, vec_can);
              //TODO: lazy cache or eager?
              std::vector< Node > vec_or;
              std::vector< Node > vec_s2;
              for(unsigned int s2i=1; s2i<x.getNumChildren(); s2i++) {
                vec_s2.push_back(x[s2i]);
              }
              Node s1 = x[0];
              Node s2 = mkConcat(vec_s2);
              for(unsigned int i=0; i<vec_can.size(); i++) {
                Node m1 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s1, vec_can[i].first);
                Node m2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s2, vec_can[i].second);
                Node c = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::AND, m1, m2) );
                vec_or.push_back( c );
              }
              Node conc = vec_or.size()==1 ? vec_or[0] : Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::OR, vec_or) );
              //Trace("regexp-split") << "R " << r << " to " << conc << std::endl;
              Node antec = mkRegExpAntec(atom, mkExplain(rnfexp));
              if(conc == d_true) {
                if(changed) {
                  cprocessed.push_back( assertion );
                } else {
                  processed.push_back( assertion );
                }
              } else if(conc == d_false) {
                conc = Node::null();
                sendLemma(antec, conc, "RegExp CST-SP Conflict");
              } else {
                sendLemma(antec, conc, "RegExp-CST-SP");
              }
              addedLemma = true;
              flag = false;
            }
          }
        } else {
          if(! options::stringExp()) {
            throw LogicException("Strings Incomplete (due to Negative Membership) by default, try --strings-exp option.");
          }
        }
        if(flag) {
          //check if the term is atomic
          Node xr = getRepresentative( x );
          //Trace("strings-regexp") << xr << " is rep of " << x << std::endl;
          //Assert( d_normal_forms.find( xr )!=d_normal_forms.end() );
          //TODO
          if( true || r.getKind()!=kind::REGEXP_STAR || ( d_normal_forms[xr].size()==1 && x.getKind()!=kind::STRING_CONCAT ) ){
            Trace("strings-regexp") << "Unroll/simplify membership of atomic term " << xr << std::endl;
            //if so, do simple unrolling
            std::vector< Node > nvec;

            /*if(xr.isConst()) {
              Node tmp = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, xr, r) );
              if(tmp==d_true || tmp==d_false) {
                if(!polarity) {
                  tmp = tmp==d_true? d_false : d_true;
                }
                nvec.push_back( tmp );
              }
            }*/

            if(nvec.empty()) {
              d_regexp_opr.simplify(atom, nvec, polarity);
            }
            Node antec = assertion;
            if(d_regexp_ant.find(assertion) != d_regexp_ant.end()) {
              antec = d_regexp_ant[assertion];
              for(std::vector< Node >::const_iterator itr=nvec.begin(); itr<nvec.end(); itr++) {
                if(itr->getKind() == kind::STRING_IN_REGEXP) {
                  if(d_regexp_ant.find( *itr ) == d_regexp_ant.end()) {
                    d_regexp_ant[ *itr ] = antec;
                  }
                }
              }
            }
            antec = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::AND, antec, mkExplain(rnfexp)) );
            Node conc = nvec.size()==1 ? nvec[0] :
                NodeManager::currentNM()->mkNode(kind::AND, nvec);
            conc = Rewriter::rewrite(conc);
            sendLemma( antec, conc, "REGEXP" );
            addedLemma = true;
            if(changed) {
              cprocessed.push_back( assertion );
            } else {
              processed.push_back( assertion );
            }
            //d_regexp_ucached[assertion] = true;
          } else {
            Trace("strings-regexp") << "Unroll/simplify membership of non-atomic term " << xr << " = ";
            for( unsigned j=0; j<d_normal_forms[xr].size(); j++ ){
              Trace("strings-regexp") << d_normal_forms[xr][j] << " ";
            }
            Trace("strings-regexp") << ", polarity = " << polarity << std::endl;
            //otherwise, distribute unrolling over parts
            Node p1;
            Node p2;
            if( d_normal_forms[xr].size()>1 ){
              p1 = d_normal_forms[xr][0];
              std::vector< Node > cc;
              cc.insert( cc.begin(), d_normal_forms[xr].begin() + 1, d_normal_forms[xr].end() );
              p2 = mkConcat( cc );
            }

            Trace("strings-regexp-debug") << "Construct antecedant..." << std::endl;
            std::vector< Node > antec;
            std::vector< Node > antecn;
            antec.insert( antec.begin(), d_normal_forms_exp[xr].begin(), d_normal_forms_exp[xr].end() );
            if( x!=xr ){
              antec.push_back( x.eqNode( xr ) );
            }
            antecn.push_back( assertion );
            Node ant = mkExplain( antec, antecn );
            Trace("strings-regexp-debug") << "Construct conclusion..." << std::endl;
            Node conc;
            if( polarity ){
              if( d_normal_forms[xr].size()==0 ){
                conc = d_true;
              }else if( d_normal_forms[xr].size()==1 ){
                Trace("strings-regexp-debug") << "Case 1\n";
                conc = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, d_normal_forms[xr][0], r);
              }else{
                Trace("strings-regexp-debug") << "Case 2\n";
                std::vector< Node > conc_c;
                Node s11 = mkSkolemS( "s11" );
                Node s12 = mkSkolemS( "s12" );
                Node s21 = mkSkolemS( "s21" );
                Node s22 = mkSkolemS( "s22" );
                conc = p1.eqNode( mkConcat(s11, s12) );
                conc_c.push_back(conc);
                conc = p2.eqNode( mkConcat(s21, s22) );
                conc_c.push_back(conc);
                conc = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s11, r);
                conc_c.push_back(conc);
                conc = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP,  mkConcat(s12, s21), r[0]);
                conc_c.push_back(conc);
                conc = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s22, r);
                conc_c.push_back(conc);
                conc = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, conc_c));
                Node eqz = Rewriter::rewrite(x.eqNode(d_emptyString));
                conc = NodeManager::currentNM()->mkNode(kind::OR, eqz, conc);
                d_pending_req_phase[eqz] = true;
              }
            }else{
              if( d_normal_forms[xr].size()==0 ){
                conc = d_false;
              }else if( d_normal_forms[xr].size()==1 ){
                Trace("strings-regexp-debug") << "Case 3\n";
                conc = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, d_normal_forms[xr][0], r).negate();
              }else{
                Trace("strings-regexp-debug") << "Case 4\n";
                Node len1 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, p1);
                Node len2 = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, p2);
                Node bi = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
                Node bj = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
                Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, bi, bj);
                Node g1 = NodeManager::currentNM()->mkNode(kind::AND,
                      NodeManager::currentNM()->mkNode(kind::GEQ, bi, d_zero),
                      NodeManager::currentNM()->mkNode(kind::GEQ, len1, bi),
                      NodeManager::currentNM()->mkNode(kind::GEQ, bj, d_zero),
                      NodeManager::currentNM()->mkNode(kind::GEQ, len2, bj));
                Node s11 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, p1, d_zero, bi);
                Node s12 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, p1, bi, NodeManager::currentNM()->mkNode(kind::MINUS, len1, bi));
                Node s21 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, p2, d_zero, bj);
                Node s22 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, p2, bj, NodeManager::currentNM()->mkNode(kind::MINUS, len2, bj));
                Node cc1 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s11, r).negate();
                Node cc2 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP,  mkConcat(s12, s21), r[0]).negate();
                Node cc3 = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, s22, r).negate();
                conc = NodeManager::currentNM()->mkNode(kind::OR, cc1, cc2, cc3);
                conc = NodeManager::currentNM()->mkNode(kind::IMPLIES, g1, conc);
                conc = NodeManager::currentNM()->mkNode(kind::FORALL, b1v, conc);
                conc = NodeManager::currentNM()->mkNode(kind::AND, x.eqNode(d_emptyString).negate(), conc);
              }
            }
            if( conc!=d_true ){
              ant = mkRegExpAntec(assertion, ant);
              sendLemma(ant, conc, "REGEXP CSTAR");
              addedLemma = true;
              if( conc==d_false ){
                d_regexp_ccached.insert( assertion );
              }else{
                cprocessed.push_back( assertion );
              }
            }else{
              d_regexp_ccached.insert(assertion);
            }
          }
        }
      }
      if(d_conflict) {
        break;
      }
    }
  }
  if( addedLemma ) {
    if( !d_conflict ){
      for( unsigned i=0; i<processed.size(); i++ ) {
        d_regexp_ucached.insert(processed[i]);
      }
      for( unsigned i=0; i<cprocessed.size(); i++ ) {
        d_regexp_ccached.insert(cprocessed[i]);
      }
    }
  }
}

bool TheoryStrings::checkPDerivative(Node x, Node r, Node atom, bool &addedLemma,
  std::vector< Node > &processed, std::vector< Node > &cprocessed, std::vector< Node > &nf_exp) {
  /*if(d_opt_regexp_gcd) {
    if(d_membership_length.find(atom) == d_membership_length.end()) {
      addedLemma = addMembershipLength(atom);
      d_membership_length[atom] = true;
    } else {
      Trace("strings-regexp") << "Membership length is already added." << std::endl;
    }
  }*/
  Node antnf = mkExplain(nf_exp);

  if(areEqual(x, d_emptyString)) {
    Node exp;
    switch(d_regexp_opr.delta(r, exp)) {
      case 0: {
        Node antec = mkRegExpAntec(atom, x.eqNode(d_emptyString));
        antec = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, antec, antnf));
        sendLemma(antec, exp, "RegExp Delta");
        addedLemma = true;
        d_regexp_ccached.insert(atom);
        return false;
      }
      case 1: {
        d_regexp_ccached.insert(atom);
        break;
      }
      case 2: {
        Node antec = mkRegExpAntec(atom, x.eqNode(d_emptyString));
        antec = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, antec, antnf));
        Node conc = Node::null();
        sendLemma(antec, conc, "RegExp Delta CONFLICT");
        addedLemma = true;
        d_regexp_ccached.insert(atom);
        return false;
      }
      default:
        //Impossible
        break;
    }
  } else {
    /*Node xr = getRepresentative( x );
    if(x != xr) {
      Node n = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, xr, r);
      Node nn = Rewriter::rewrite( n );
      if(nn == d_true) {
        d_regexp_ccached.insert(atom);
        return false;
      } else if(nn == d_false) {
        Node antec = mkRegExpAntec(atom, x.eqNode(xr));
        Node conc = Node::null();
        sendLemma(antec, conc, "RegExp Delta CONFLICT");
        addedLemma = true;
        d_regexp_ccached.insert(atom);
        return false;
      }
    }*/
    Node sREant = mkRegExpAntec(atom, d_true);
    sREant = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, sREant, antnf));
    if(deriveRegExp( x, r, sREant )) {
      addedLemma = true;
      processed.push_back( atom );
      return false;
    }
  }
  return true;
}

void TheoryStrings::checkInit() {
  //build term index
  d_eqc_to_const.clear();
  d_eqc_to_const_base.clear();
  d_eqc_to_const_exp.clear();
  d_term_index.clear();
  d_strings_eqc.clear();

  std::map< Kind, unsigned > ncongruent;
  std::map< Kind, unsigned > congruent;
  d_emptyString_r = getRepresentative( d_emptyString );
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if( !tn.isInteger() && !tn.isRegExp() ){
      if( tn.isString() ){
        d_strings_eqc.push_back( eqc );
      }
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
      while( !eqc_i.isFinished() ) {
        Node n = *eqc_i;
        if( n.isConst() ){
          d_eqc_to_const[eqc] = n;
          d_eqc_to_const_base[eqc] = n;
          d_eqc_to_const_exp[eqc] = Node::null();
        }else if( n.getNumChildren()>0 ){
          Kind k = n.getKind();
          if( k!=kind::EQUAL ){
            if( std::find( d_congruent.begin(), d_congruent.end(), n )==d_congruent.end() ){
              std::vector< Node > c;
              Node nc = d_term_index[k].add( n, 0, this, d_emptyString_r, c );
              if( nc!=n ){
                //check if we have inferred a new equality by removal of empty components
                if( n.getKind()==kind::STRING_CONCAT && !areEqual( nc, n ) ){
                  std::vector< Node > exp;
                  unsigned count[2] = { 0, 0 };
                  while( count[0]<nc.getNumChildren() || count[1]<n.getNumChildren() ){
                    //explain empty prefixes
                    for( unsigned t=0; t<2; t++ ){
                      Node nn = t==0 ? nc : n;
                      while( count[t]<nn.getNumChildren() &&
                            ( nn[count[t]]==d_emptyString || areEqual( nn[count[t]], d_emptyString ) ) ){
                        if( nn[count[t]]!=d_emptyString ){
                          exp.push_back( nn[count[t]].eqNode( d_emptyString ) );
                        }
                        count[t]++;
                      }
                    }
                    //explain equal components
                    if( count[0]<nc.getNumChildren() ){
                      Assert( count[1]<n.getNumChildren() );
                      if( nc[count[0]]!=n[count[1]] ){
                        exp.push_back( nc[count[0]].eqNode( n[count[1]] ) );
                      }
                      count[0]++;
                      count[1]++;
                    }
                  }
                  //infer the equality
                  sendInfer( mkAnd( exp ), n.eqNode( nc ), "I_Norm" );
                }else{
                  //update the extf map : only process if neither has been reduced
                  NodeBoolMap::const_iterator it = d_ext_func_terms.find( n );
                  if( it!=d_ext_func_terms.end() ){
                    if( d_ext_func_terms.find( nc )==d_ext_func_terms.end() ){
                      d_ext_func_terms[nc] = (*it).second;
                    }else{
                      d_ext_func_terms[nc] = d_ext_func_terms[nc] && (*it).second;
                    }
                    d_ext_func_terms[n] = false;
                  }
                }
                //this node is congruent to another one, we can ignore it
                Trace("strings-process-debug") << "  congruent term : " << n << std::endl;
                d_congruent.push_back( n );
                congruent[k]++;
              }else if( k==kind::STRING_CONCAT && c.size()==1 ){
                Trace("strings-process-debug") << "  congruent term by singular : " << n << " " << c[0] << std::endl;
                //singular case
                if( !areEqual( c[0], n ) ){
                  std::vector< Node > exp;
                  //explain empty components
                  bool foundNEmpty = false;
                  for( unsigned i=0; i<n.getNumChildren(); i++ ){
                    if( areEqual( n[i], d_emptyString ) ){
                      if( n[i]!=d_emptyString ){
                        exp.push_back( n[i].eqNode( d_emptyString ) );
                      }
                    }else{
                      Assert( !foundNEmpty );
                      if( n[i]!=c[0] ){
                        exp.push_back( n[i].eqNode( c[0] ) );
                      }
                      foundNEmpty = true;
                    }
                  }
                  AlwaysAssert( foundNEmpty );
                  //infer the equality
                  sendInfer( mkAnd( exp ), n.eqNode( c[0] ), "I_Norm_S" );
                }
                d_congruent.push_back( n );
                congruent[k]++;
              }else{
                ncongruent[k]++;
              }
            }else{
              congruent[k]++;
            }
          }
        }
        ++eqc_i;
      }
    }
    ++eqcs_i;
  }
  if( Trace.isOn("strings-process") ){
    for( std::map< Kind, TermIndex >::iterator it = d_term_index.begin(); it != d_term_index.end(); ++it ){
      Trace("strings-process") << "  Terms[" << it->first << "] = " << ncongruent[it->first] << "/" << (congruent[it->first]+ncongruent[it->first]) << std::endl;
    }
  }
  Trace("strings-process") << "Done check init, addedLemma = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
  //now, infer constants for equivalence classes
  if( !hasProcessed() ){
    //do fixed point
    unsigned prevSize;
    do{
      Trace("strings-process-debug") << "Check constant equivalence classes..." << std::endl;
      prevSize = d_eqc_to_const.size();
      std::vector< Node > vecc;
      checkConstantEquivalenceClasses( &d_term_index[kind::STRING_CONCAT], vecc );
    }while( !hasProcessed() && d_eqc_to_const.size()>prevSize );
    Trace("strings-process") << "Done check constant equivalence classes, addedLemma = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
  }
}

void TheoryStrings::checkConstantEquivalenceClasses( TermIndex* ti, std::vector< Node >& vecc ) {
  Node n = ti->d_data;
  if( !n.isNull() ){
    //construct the constant
    Node c = mkConcat( vecc );
    if( !areEqual( n, c ) ){
      Trace("strings-debug") << "Constant eqc : " << c << " for " << n << std::endl;
      Trace("strings-debug") << "  ";
      for( unsigned i=0; i<vecc.size(); i++ ){
        Trace("strings-debug") << vecc[i] << " ";
      }
      Trace("strings-debug") << std::endl;
      unsigned count = 0;
      unsigned countc = 0;
      std::vector< Node > exp;
      while( count<n.getNumChildren() ){
        while( count<n.getNumChildren() && areEqual( n[count], d_emptyString ) ){
          addToExplanation( n[count], d_emptyString, exp );
          count++;
        }
        if( count<n.getNumChildren() ){
          Trace("strings-debug") << "...explain " << n[count] << " " << vecc[countc] << std::endl;
          if( !areEqual( n[count], vecc[countc] ) ){
            Node nrr = getRepresentative( n[count] );
            Assert( !d_eqc_to_const_exp[nrr].isNull() );
            addToExplanation( n[count], d_eqc_to_const_base[nrr], exp );
            exp.push_back( d_eqc_to_const_exp[nrr] );
          }else{
            addToExplanation( n[count], vecc[countc], exp );
          }
          countc++;
          count++;
        }
      }
      //exp contains an explanation of n==c
      Assert( countc==vecc.size() );
      if( hasTerm( c ) ){
        sendInfer( mkAnd( exp ), n.eqNode( c ), "I_CONST_MERGE" );
        return;
      }else if( !hasProcessed() ){
        Node nr = getRepresentative( n );
        std::map< Node, Node >::iterator it = d_eqc_to_const.find( nr );
        if( it==d_eqc_to_const.end() ){
          Trace("strings-debug") << "Set eqc const " << n << " to " << c << std::endl;
          d_eqc_to_const[nr] = c;
          d_eqc_to_const_base[nr] = n;
          d_eqc_to_const_exp[nr] = mkAnd( exp );
        }else if( c!=it->second ){
          //conflict
          Trace("strings-debug") << "Conflict, other constant was " << it->second << ", this constant was " << c << std::endl;
          if( d_eqc_to_const_exp[nr].isNull() ){
            // n==c ^ n == c' => false
            addToExplanation( n, it->second, exp );
          }else{
            // n==c ^ n == d_eqc_to_const_base[nr] == c' => false
            exp.push_back( d_eqc_to_const_exp[nr] );
            addToExplanation( n, d_eqc_to_const_base[nr], exp );
          }
          sendLemma( mkExplain( exp ), d_false, "I_CONST_CONFLICT" );
          return;
        }else{
          Trace("strings-debug") << "Duplicate constant." << std::endl;
        }
      }
    }
  }
  for( std::map< Node, TermIndex >::iterator it = ti->d_children.begin(); it != ti->d_children.end(); ++it ){
    std::map< Node, Node >::iterator itc = d_eqc_to_const.find( it->first );
    if( itc!=d_eqc_to_const.end() ){
      vecc.push_back( itc->second );
      checkConstantEquivalenceClasses( &it->second, vecc );
      vecc.pop_back();
      if( hasProcessed() ){
        break;
      }
    }
  }
}

void TheoryStrings::checkExtendedFuncsEval( int effort ) {
  Trace("strings-extf-debug") << "Checking " << d_ext_func_terms.size() << " extended functions." << std::endl;
  for( NodeBoolMap::iterator it = d_ext_func_terms.begin(); it != d_ext_func_terms.end(); ++it ){
    if( (*it).second ){
      Node n = (*it).first;
      Trace("strings-extf-debug") << "Check extf " << n << "..." << std::endl;
      //check if all children are in eqc with a constant, if so, we can rewrite
      std::vector< Node > children;
      std::vector< Node > exp;
      std::map< Node, Node > visited;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = inferConstantDefinition( n[i], exp, visited );
        if( !nc.isNull() ){
          Trace("strings-extf-debug") << "  child " << i << " : " << nc << std::endl;
          children.push_back( nc );
          Assert( nc.getType()==n[i].getType() );
        }else{
          if( effort>0 ){
            //get the normalized string
            nc = getNormalString( n[i], exp );
            children.push_back( nc );
          }else{
            Trace("strings-extf-debug") << "  unresolved due to " << n[i] << std::endl;
            break;
          }
        }
      }
      if( children.size()==n.getNumChildren() ){
        if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
          children.insert(children.begin(),n.getOperator());
        }
        Node nr = NodeManager::currentNM()->mkNode( n.getKind(), children );
        Node nrc = Rewriter::rewrite( nr );
        if( nrc.isConst() ){
          //mark as reduced
          d_ext_func_terms[n] = false;
          Trace("strings-extf-debug") << "  resolvable by evaluation..." << std::endl;
          std::vector< Node > exps;
          Trace("strings-extf-debug") << "  get symbolic definition..." << std::endl;
          Node nrs = getSymbolicDefinition( nr, exps );
          if( !nrs.isNull() ){
            Trace("strings-extf-debug") << "  rewrite " << nrs << "..." << std::endl;
            nrs = Rewriter::rewrite( nrs );
            //ensure the symbolic form is non-trivial
            if( nrs.isConst() ){
              Trace("strings-extf-debug") << "  symbolic definition is trivial..." << std::endl;
              nrs = Node::null();
            }
          }else{
            Trace("strings-extf-debug") << "  could not infer symbolic definition." << std::endl;
          }
          Node conc;
          if( !nrs.isNull() ){
            Trace("strings-extf-debug") << "  symbolic def : " << nrs << std::endl;
            if( !areEqual( nrs, nrc ) ){
              //infer symbolic unit
              if( n.getType().isBoolean() ){
                conc = nrc==d_true ? nrs : nrs.negate();
              }else{
                conc = nrs.eqNode( nrc );
              }
              exp.clear();
            }
          }else{
            if( !areEqual( n, nrc ) ){
              if( n.getType().isBoolean() ){
                exp.push_back( nrc==d_true ? n.negate() : n );
                conc = d_false;
              }else{
                conc = n.eqNode( nrc );
              }
            }
          }
          if( !conc.isNull() ){
            Trace("strings-extf") << "  resolve extf : " << nr << " -> " << nrc << std::endl;
            if( n.getType().isInteger() || exp.empty() ){
              sendLemma( mkExplain( exp ), conc, effort==0 ? "EXTF" : "EXTF-N" );
            }else{
              sendInfer( mkAnd( exp ), conc, effort==0 ? "EXTF" : "EXTF-N" );
            }
            if( d_conflict ){
              Trace("strings-extf") << "  conflict, return." << std::endl;
              return;
            }
          }
        }else{
          Trace("strings-extf-debug") << "  could not rewrite : " << nr  << std::endl;
        }
      }
    }
  }
}

Node TheoryStrings::inferConstantDefinition( Node n, std::vector< Node >& exp, std::map< Node, Node >& visited ) {
  if( n.isConst() ){
    return n;
  }else{
    Node nr = getRepresentative( n );
    std::map< Node, Node >::iterator it = visited.find( nr );
    if( it==visited.end() ){
      visited[nr] = Node::null();
      if( nr.isConst() ){
        addToExplanation( n, nr, exp );
        visited[nr] = nr;
        return nr;
      }else{
        std::map< Node, Node >::iterator itc = d_eqc_to_const.find( nr );
        if( itc!=d_eqc_to_const.end() ){
          exp.push_back( n.eqNode( d_eqc_to_const_base[nr] ) );
          if( !d_eqc_to_const_exp[nr].isNull() ){
            exp.push_back( d_eqc_to_const_exp[nr] );
          }
          visited[nr] = itc->second;
          return itc->second;
        }else{
          if( n.getNumChildren()>0 ){
            std::vector< Node > children;
            for( unsigned i=0; i<n.getNumChildren(); i++ ){
              Node nic = inferConstantDefinition( n[i], exp, visited );
              if( nic.isNull() ){
                break;
              }else{
                children.push_back( nic );
              }
            }
            if( children.size()==n.getNumChildren() ){
              if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
                children.insert(children.begin(),n.getOperator());
              }
              Node ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
              visited[nr] = ret;
              return ret;
            }
          }
        }
      }
    }else{
      return it->second;
    }
  }
  return Node::null();
}

Node TheoryStrings::getSymbolicDefinition( Node n, std::vector< Node >& exp ) {
  if( n.getNumChildren()==0 ){
    NodeNodeMap::const_iterator it = d_proxy_var.find( n );
    if( it==d_proxy_var.end() ){
      return Node::null();
    }else{
      Node eq = n.eqNode( (*it).second );
      eq = Rewriter::rewrite( eq );
      if( std::find( exp.begin(), exp.end(), eq )==exp.end() ){
        exp.push_back( eq );
      }
      return (*it).second;
    }
  }else{
    std::vector< Node > children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      children.push_back( n.getOperator() );
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( n.getKind()==kind::STRING_IN_REGEXP && i==1 ){
        children.push_back( n[i] );
      }else{
        Node ns = getSymbolicDefinition( n[i], exp );
        if( ns.isNull() ){
          return Node::null();
        }else{
          children.push_back( ns );
        }
      }
    }
    return NodeManager::currentNM()->mkNode( n.getKind(), children );
  }
}

void TheoryStrings::checkExtendedFuncs() {
  std::map< bool, std::vector< Node > > pnContains;
  std::map< bool, std::vector< Node > > pnMem;
  for( NodeBoolMap::iterator it = d_ext_func_terms.begin(); it != d_ext_func_terms.end(); ++it ){
    if( (*it).second ){
      Node n = (*it).first;
      if( n.getKind()==kind::STRING_STRCTN ) {
        bool pol = areEqual( n, d_true );
        Assert( pol || areEqual( n, d_false ) );
        pnContains[pol].push_back( n );
      }
#ifdef LAZY_ADD_MEMBERSHIP
      else if( n.getKind()==kind::STRING_IN_REGEXP ) {
        bool pol = areEqual( n, d_true );
        Assert( pol || areEqual( n, d_false ) );
        pnMem[pol].push_back( n );
      }
#endif
    }
  }

  checkPosContains( pnContains[true] );
  Trace("strings-process") << "Done check positive contain constraints, addedLemma = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
  if( !hasProcessed() ) {
    checkNegContains( pnContains[false] );
    Trace("strings-process") << "Done check negative contain constraints, addedLemma = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
    if( !hasProcessed() ) {
      Trace("strings-process") << "Adding memberships..." << std::endl;
      //add all non-evaluated memberships
#ifdef LAZY_ADD_MEMBERSHIP
      for( std::map< bool, std::vector< Node > >::iterator it=pnMem.begin(); it != pnMem.end(); ++it ){
        for( unsigned i=0; i<it->second.size(); i++ ){
          addMembership( it->first ? it->second[i] : it->second[i].negate() );
        }
      }
#endif
      checkMemberships();
      Trace("strings-process") << "Done check memberships, addedLemma = " << !d_pending.empty() << " " << !d_lemma_cache.empty() << ", d_conflict = " << d_conflict << std::endl;
    }
  }
}

void TheoryStrings::checkPosContains( std::vector< Node >& posContains ) {
  for( unsigned i=0; i<posContains.size(); i++ ) {
    if( !d_conflict ){
      Node atom = posContains[i];
      Trace("strings-ctn") << "We have positive contain assertion : " << atom << std::endl;
      Assert( atom.getKind()==kind::STRING_STRCTN );
      Node x = atom[0];
      Node s = atom[1];
      if( !areEqual( s, d_emptyString ) && !areEqual( s, x ) ) {
        if(d_pos_ctn_cached.find(atom) == d_pos_ctn_cached.end()) {
          Node sk1 = mkSkolemS( "sc1" );
          Node sk2 = mkSkolemS( "sc2" );
          Node eq = Rewriter::rewrite( x.eqNode( mkConcat( sk1, s, sk2 ) ) );
          sendLemma( atom, eq, "POS-INC" );
          d_pos_ctn_cached.insert( atom );
          Trace("strings-ctn") << "... add lemma: " << eq << std::endl;
        } else {
          Trace("strings-ctn") << "... is already rewritten." << std::endl;
        }
      } else {
        Trace("strings-ctn") << "... is satisfied." << std::endl;
      }
    }
  }
}

void TheoryStrings::checkNegContains( std::vector< Node >& negContains ) {
  //check for conflicts
  for( unsigned i=0; i<negContains.size(); i++ ){
    if( !d_conflict ){
      Node atom = negContains[i];
      Trace("strings-ctn") << "We have negative contain assertion : (not " << atom << " )" << std::endl;
      if( areEqual( atom[1], d_emptyString ) ) {
        Node ant = NodeManager::currentNM()->mkNode( kind::AND, atom.negate(), atom[1].eqNode( d_emptyString ) );
        Node conc = Node::null();
        sendLemma( ant, conc, "NEG-CTN Conflict 1" );
      } else if( areEqual( atom[1], atom[0] ) ) {
        Node ant = NodeManager::currentNM()->mkNode( kind::AND, atom.negate(), atom[1].eqNode( atom[0] ) );
        Node conc = Node::null();
        sendLemma( ant, conc, "NEG-CTN Conflict 2" );
      }
    }
  }
  if( !d_conflict ){
    //check for lemmas
    if(options::stringExp()) {
      for( unsigned i=0; i<negContains.size(); i++ ){
        Node atom = negContains[i];
        Node x = atom[0];
        Node s = atom[1];
        Node lenx = getLength(x);
        Node lens = getLength(s);
        if(areEqual(lenx, lens)) {
          if(d_neg_ctn_eqlen.find(atom) == d_neg_ctn_eqlen.end()) {
            Node eq = lenx.eqNode(lens);
            Node antc = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, atom.negate(), eq ) );
            Node xneqs = x.eqNode(s).negate();
            d_neg_ctn_eqlen.insert( atom );
            sendLemma( antc, xneqs, "NEG-CTN-EQL" );
          }
        } else if(!areDisequal(lenx, lens)) {
          if(d_neg_ctn_ulen.find(atom) == d_neg_ctn_ulen.end()) {
            lenx = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x);
            lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s);
            d_neg_ctn_ulen.insert( atom );
            sendSplit(lenx, lens, "NEG-CTN-SP");
          }
        } else {
          if(d_neg_ctn_cached.find(atom) == d_neg_ctn_cached.end()) {
            lenx = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x);
            lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, s);
            Node b1 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
            Node b1v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b1);
            Node g1 = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::AND, NodeManager::currentNM()->mkNode( kind::GEQ, b1, d_zero ),
                  NodeManager::currentNM()->mkNode( kind::GEQ, NodeManager::currentNM()->mkNode( kind::MINUS, lenx, lens ), b1 ) ) );
            Node b2 = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
            Node s2 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, x, NodeManager::currentNM()->mkNode( kind::PLUS, b1, b2 ), d_one);
            Node s5 = NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, s, b2, d_one);

            Node b2v = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, b2);//, s1, s3, s4, s6);

            std::vector< Node > vec_nodes;
            Node cc = NodeManager::currentNM()->mkNode( kind::GEQ, b2, d_zero );
            vec_nodes.push_back(cc);
            cc = NodeManager::currentNM()->mkNode( kind::GT, lens, b2 );
            vec_nodes.push_back(cc);

            cc = s2.eqNode(s5).negate();
            vec_nodes.push_back(cc);

            Node conc = NodeManager::currentNM()->mkNode(kind::AND, vec_nodes);
            conc = NodeManager::currentNM()->mkNode( kind::EXISTS, b2v, conc );
            conc = NodeManager::currentNM()->mkNode( kind::IMPLIES, g1, conc );
            conc = NodeManager::currentNM()->mkNode( kind::FORALL, b1v, conc );
            Node xlss = NodeManager::currentNM()->mkNode( kind::GT, lens, lenx );
            conc = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::OR, xlss, conc ) );

            d_neg_ctn_cached.insert( atom );
            sendLemma( atom.negate(), conc, "NEG-CTN-BRK" );
            //d_pending_req_phase[xlss] = true;
          }
        }
      }
    } else {
      if( !negContains.empty() ){
        throw LogicException("Strings Incomplete (due to Negative Contain) by default, try --strings-exp option.");
      }
    }
  }
}

void TheoryStrings::checkExtendedFuncsReduction() {
  //very lazy reduction?
  /*
  if( options::stringLazyPreproc() ){
    for( NodeBoolMap::iterator it = d_ext_func_terms.begin(); it != d_ext_func_terms.end(); ++it ){
      if( (*it).second ){
        Node n = (*it).first;
        if( n.getKind()!=kind::STRING_IN_REGEXP ){
          if( d_preproc_cache.find( n )==d_preproc_cache.end() ){
            d_preproc_cache[n] = true;
            std::vector< Node > new_nodes;
            Node res = d_preproc.decompose( n, new_nodes );
            Assert( res==n );
            if( !new_nodes.empty() ){
              Node nnlem = new_nodes.size()==1 ? new_nodes[0] : NodeManager::currentNM()->mkNode( kind::AND, new_nodes );
              nnlem = Rewriter::rewrite( nnlem );
              Trace("strings-pp-lemma") << "Reduction lemma : " << nnlem << std::endl;
              Trace("strings-pp-lemma") << "...from term " << n << std::endl;
              d_out->lemma( nnlem );
              addedLemmas = true;
            }
          }
        }
      }
    }
  }
  */
}


CVC4::String TheoryStrings::getHeadConst( Node x ) {
  if( x.isConst() ) {
    return x.getConst< String >();
  } else if( x.getKind() == kind::STRING_CONCAT ) {
    if( x[0].isConst() ) {
      return x[0].getConst< String >();
    } else {
      return d_emptyString.getConst< String >();
    }
  } else {
    return d_emptyString.getConst< String >();
  }
}

bool TheoryStrings::addMembershipLength(Node atom) {
  //Node x = atom[0];
  //Node r = atom[1];

  /*std::vector< int > co;
  co.push_back(0);
  for(unsigned int k=0; k<lts.size(); ++k) {
    if(lts[k].isConst() && lts[k].getType().isInteger()) {
      int len = lts[k].getConst<Rational>().getNumerator().toUnsignedInt();
      co[0] += cols[k].size() * len;
    } else {
      co.push_back( cols[k].size() );
    }
  }
  int g_co = co[0];
  for(unsigned k=1; k<co.size(); ++k) {
    g_co = gcd(g_co, co[k]);
  }*/
  return false;
}

bool TheoryStrings::deriveRegExp( Node x, Node r, Node ant ) {
  // TODO cstr in vre
  Assert(x != d_emptyString);
  Trace("regexp-derive") << "TheoryStrings::deriveRegExp: x=" << x << ", r= " << r << std::endl;
  //if(x.isConst()) {
  //  Node n = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r );
  //  Node r = Rewriter::rewrite( n );
  //  if(n != r) {
  //    sendLemma(ant, r, "REGEXP REWRITE");
  //    return true;
  //  }
  //}
  CVC4::String s = getHeadConst( x );
  if( !s.isEmptyString() && d_regexp_opr.checkConstRegExp( r ) ) {
    Node conc = Node::null();
    Node dc = r;
    bool flag = true;
    for(unsigned i=0; i<s.size(); ++i) {
      CVC4::String c = s.substr(i, 1);
      Node dc2;
      int rt = d_regexp_opr.derivativeS(dc, c, dc2);
      dc = dc2;
      if(rt == 0) {
        //TODO
      } else if(rt == 2) {
        // CONFLICT
        flag = false;
        break;
      }
    }
    // send lemma
    if(flag) {
      if(x.isConst()) {
        Assert(false, "Impossible: TheoryStrings::deriveRegExp: const string in const regular expression.");
        return false;
      } else {
        Assert( x.getKind() == kind::STRING_CONCAT );
        std::vector< Node > vec_nodes;
        for(unsigned int i=1; i<x.getNumChildren(); ++i ) {
          vec_nodes.push_back( x[i] );
        }
        Node left =  mkConcat( vec_nodes );
        left = Rewriter::rewrite( left );
        conc = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, left, dc );

        /*std::vector< Node > sdc;
        d_regexp_opr.simplify(conc, sdc, true);
        if(sdc.size() == 1) {
          conc = sdc[0];
        } else {
          conc = Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::AND, conc));
        }*/
      }
    }
    sendLemma(ant, conc, "RegExp-Derive");
    return true;
  } else {
    return false;
  }
}

void TheoryStrings::addMembership(Node assertion) {
  bool polarity = assertion.getKind() != kind::NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Node x = atom[0];
  Node r = atom[1];
  if(polarity) {
    NodeList* lst;
    NodeListMap::iterator itr_xr = d_pos_memberships.find( x );
    if( itr_xr == d_pos_memberships.end() ){
      lst = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
      d_pos_memberships.insertDataFromContextMemory( x, lst );
    } else {
      lst = (*itr_xr).second;
    }
    //check
    for( NodeList::const_iterator itr = lst->begin(); itr != lst->end(); ++itr ) {
      if( r == *itr ) {
        return;
      }
    }
    lst->push_back( r );
  } else if(!options::stringIgnNegMembership()) {
    /*if(options::stringEIT() && d_regexp_opr.checkConstRegExp(r)) {
      int rt;
      Node r2 = d_regexp_opr.complement(r, rt);
      Node a = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, x, r2);
    }*/
    NodeList* lst;
    NodeListMap::iterator itr_xr = d_neg_memberships.find( x );
    if( itr_xr == d_neg_memberships.end() ){
      lst = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
      d_neg_memberships.insertDataFromContextMemory( x, lst );
    } else {
      lst = (*itr_xr).second;
    }
    //check
    for( NodeList::const_iterator itr = lst->begin(); itr != lst->end(); ++itr ) {
      if( r == *itr ) {
        return;
      }
    }
    lst->push_back( r );
  }
  // old
  if(polarity || !options::stringIgnNegMembership()) {
    d_regexp_memberships.push_back( assertion );
  }
}

Node TheoryStrings::getNormalString( Node x, std::vector<Node> &nf_exp ){
  if( !x.isConst() ){
    Node xr = getRepresentative( x );
    if( d_normal_forms.find( xr ) != d_normal_forms.end() ){
      Node ret = mkConcat( d_normal_forms[xr] );
      nf_exp.insert( nf_exp.end(), d_normal_forms_exp[xr].begin(), d_normal_forms_exp[xr].end() );
      addToExplanation( x, d_normal_forms_base[xr], nf_exp );
      Trace("strings-debug") << "Term: " << x << " has a normal form " << ret << std::endl;
      return ret;
    } else {
      if(x.getKind() == kind::STRING_CONCAT) {
        std::vector< Node > vec_nodes;
        for(unsigned i=0; i<x.getNumChildren(); i++) {
          Node nc = getNormalString( x[i], nf_exp );
          vec_nodes.push_back( nc );
        }
        return mkConcat( vec_nodes );
      }
    }
  }
  return x;
}

Node TheoryStrings::getNormalSymRegExp(Node r, std::vector<Node> &nf_exp) {
  Node ret = r;
  switch( r.getKind() ) {
    case kind::REGEXP_EMPTY:
    case kind::REGEXP_SIGMA:
      break;
    case kind::STRING_TO_REGEXP: {
      if(!r[0].isConst()) {
        Node tmp = getNormalString( r[0], nf_exp );
        if(tmp != r[0]) {
          ret = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, tmp);
        }
      }
      break;
    }
    case kind::REGEXP_CONCAT: {
      std::vector< Node > vec_nodes;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        vec_nodes.push_back( getNormalSymRegExp(r[i], nf_exp) );
      }
      ret = mkConcat(vec_nodes);
      break;
    }
    case kind::REGEXP_UNION: {
      std::vector< Node > vec_nodes;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        vec_nodes.push_back( getNormalSymRegExp(r[i], nf_exp) );
      }
      ret = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec_nodes) );
      break;
    }
    case kind::REGEXP_INTER: {
      std::vector< Node > vec_nodes;
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        vec_nodes.push_back( getNormalSymRegExp(r[i], nf_exp) );
      }
      ret = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::REGEXP_INTER, vec_nodes) );
      break;
    }
    case kind::REGEXP_STAR: {
      ret = getNormalSymRegExp( r[0], nf_exp );
      ret = Rewriter::rewrite( NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, ret) );
      break;
    }
    //case kind::REGEXP_PLUS:
    //case kind::REGEXP_OPT:
    //case kind::REGEXP_RANGE:
    default: {
      Trace("strings-error") << "Unsupported term: " << r << " in normalization SymRegExp." << std::endl;
      Assert( false );
      //return Node::null();
    }
  }

  return ret;
}

//// Finite Model Finding

Node TheoryStrings::getNextDecisionRequest() {
  if(d_opt_fmf && !d_conflict) {
    Node in_var_lsum = d_input_var_lsum.get();
    //Trace("strings-fmf-debug") << "Strings::FMF: Assertion Level = " << d_valuation.getAssertionLevel() << std::endl;
    //initialize the term we will minimize
    if( in_var_lsum.isNull() && !d_input_vars.empty() ){
      Trace("strings-fmf-debug") << "Input variables: ";
      std::vector< Node > ll;
      for(NodeSet::key_iterator itr = d_input_vars.key_begin();
        itr != d_input_vars.key_end(); ++itr) {
        Trace("strings-fmf-debug") << " " << (*itr) ;
        ll.push_back( NodeManager::currentNM()->mkNode( kind::STRING_LENGTH, *itr ) );
      }
      Trace("strings-fmf-debug") << std::endl;
      in_var_lsum = ll.size()==1 ? ll[0] : NodeManager::currentNM()->mkNode( kind::PLUS, ll );
      in_var_lsum = Rewriter::rewrite( in_var_lsum );
      d_input_var_lsum.set( in_var_lsum );
    }
    if( !in_var_lsum.isNull() ){
      //Trace("strings-fmf") << "Get next decision request." << std::endl;
      //check if we need to decide on something
      int decideCard = d_curr_cardinality.get();
      if( d_cardinality_lits.find( decideCard )!=d_cardinality_lits.end() ){
        bool value;
        Node cnode = d_cardinality_lits[ d_curr_cardinality.get() ];
        if( d_valuation.hasSatValue( cnode, value ) ) {
          if( !value ){
            d_curr_cardinality.set( d_curr_cardinality.get() + 1 );
            decideCard = d_curr_cardinality.get();
            Trace("strings-fmf-debug") << "Has false SAT value, increment and decide." << std::endl;
          }else{
            decideCard = -1;
            Trace("strings-fmf-debug") << "Has true SAT value, do not decide." << std::endl;
          }
        }else{
          Trace("strings-fmf-debug") << "No SAT value, decide." << std::endl;
        }
      }
      if( decideCard!=-1 ){
        if( d_cardinality_lits.find( decideCard )==d_cardinality_lits.end() ){
          Node lit = NodeManager::currentNM()->mkNode( kind::LEQ, in_var_lsum, NodeManager::currentNM()->mkConst( Rational( decideCard ) ) );
          lit = Rewriter::rewrite( lit );
          d_cardinality_lits[decideCard] = lit;
          Node lem = NodeManager::currentNM()->mkNode( kind::OR, lit, lit.negate() );
          Trace("strings-fmf") << "Strings::FMF: Add decision lemma " << lem << ", decideCard = " << decideCard << std::endl;
          d_out->lemma( lem );
          d_out->requirePhase( lit, true );
        }
        Node lit = d_cardinality_lits[ decideCard ];
        Trace("strings-fmf") << "Strings::FMF: Decide positive on " << lit << std::endl;
        return lit;
      }
    }
  }

  return Node::null();
}

void TheoryStrings::assertNode( Node lit ) {
}

void TheoryStrings::collectExtendedFuncTerms( Node n, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==kind::STRING_SUBSTR_TOTAL || n.getKind()==kind::STRING_STRIDOF ||
        n.getKind() == kind::STRING_ITOS || n.getKind() == kind::STRING_U16TOS || n.getKind() == kind::STRING_U32TOS ||
        n.getKind() == kind::STRING_STOI || n.getKind() == kind::STRING_STOU16 || n.getKind() == kind::STRING_STOU32 ||
        n.getKind() == kind::STRING_STRREPL || n.getKind() == kind::STRING_STRCTN ){
      if( d_ext_func_terms.find( n )==d_ext_func_terms.end() ){
        Trace("strings-extf-debug") << "Found extended function : " << n << std::endl;
        d_ext_func_terms[n] = true;
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectExtendedFuncTerms( n[i], visited );
    }
  }
}

// Stats
TheoryStrings::Statistics::Statistics():
  d_splits("TheoryStrings::NumOfSplitOnDemands", 0),
  d_eq_splits("TheoryStrings::NumOfEqSplits", 0),
  d_deq_splits("TheoryStrings::NumOfDiseqSplits", 0),
  d_loop_lemmas("TheoryStrings::NumOfLoops", 0),
  d_new_skolems("TheoryStrings::NumOfNewSkolems", 0)
{
  StatisticsRegistry::registerStat(&d_splits);
  StatisticsRegistry::registerStat(&d_eq_splits);
  StatisticsRegistry::registerStat(&d_deq_splits);
  StatisticsRegistry::registerStat(&d_loop_lemmas);
  StatisticsRegistry::registerStat(&d_new_skolems);
}

TheoryStrings::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_splits);
  StatisticsRegistry::unregisterStat(&d_eq_splits);
  StatisticsRegistry::unregisterStat(&d_deq_splits);
  StatisticsRegistry::unregisterStat(&d_loop_lemmas);
  StatisticsRegistry::unregisterStat(&d_new_skolems);
}

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
