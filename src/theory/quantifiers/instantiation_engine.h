/*********************                                                        */
/*! \file instantiation_engine.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H
#define __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstStrategyUserPatterns;
class InstStrategyAutoGenTriggers;
class InstStrategyFreeVariable;
class InstStrategySimplex;
class InstStrategyCegqi;

/** instantiation strategy class */
class InstStrategy {
public:
  enum Status {
    STATUS_UNFINISHED,
    STATUS_UNKNOWN,
  };/* enum Status */
protected:
  /** reference to the instantiation engine */
  QuantifiersEngine* d_quantEngine;
public:
  InstStrategy( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  virtual ~InstStrategy(){}
  /** presolve */
  virtual void presolve() {}
  /** reset instantiation */
  virtual void processResetInstantiationRound( Theory::Effort effort ) = 0;
  /** process method, returns a status */
  virtual int process( Node f, Theory::Effort effort, int e ) = 0;
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }
  /** register quantifier */
  virtual void registerQuantifier( Node q ) {}
};/* class InstStrategy */

class InstantiationEngine : public QuantifiersModule
{
private:
  /** instantiation strategies */
  std::vector< InstStrategy* > d_instStrategies;
  /** instantiation strategies active */
  //std::map< InstStrategy*, bool > d_instStrategyActive;
  /** user-pattern instantiation strategy */
  InstStrategyUserPatterns* d_isup;
  /** auto gen triggers; only kept for destructor cleanup */
  InstStrategyAutoGenTriggers* d_i_ag;
  /** simplex (cbqi) */
  InstStrategySimplex * d_i_splx;
  /** generic cegqi */
  InstStrategyCegqi * d_i_cegqi;
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** current processing quantified formulas */
  std::vector< Node > d_quants;
  /** whether we have added cbqi lemma */
  std::map< Node, bool > d_added_cbqi_lemma;
private:
  /** has added cbqi lemma */
  bool hasAddedCbqiLemma( Node q ) { return d_added_cbqi_lemma.find( q )!=d_added_cbqi_lemma.end(); }
  /** helper functions */
  bool hasNonCbqiVariable( Node q );
  bool hasApplyUf( Node n );
  /** whether to do CBQI for quantifier q */
  bool doCbqi( Node q );
  /** is the engine incomplete for this quantifier */
  bool isIncomplete( Node q );
  /** cbqi set inactive */
  bool d_cbqi_set_quant_inactive;
private:
  /** do instantiation round */
  bool doInstantiationRound( Theory::Effort effort );
  /** register literals of n, f is the quantifier it belongs to */
  //void registerLiterals( Node n, Node f );
public:
  InstantiationEngine( QuantifiersEngine* qe );
  ~InstantiationEngine();
  /** initialize */
  void finishInit();
  void presolve();
  bool needsCheck( Theory::Effort e );
  unsigned needsModel( Theory::Effort e );
  void reset_round( Theory::Effort e );
  void check( Theory::Effort e, unsigned quant_e );
  bool checkComplete();
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  Node getNextDecisionRequest();
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
  void addUserNoPattern( Node f, Node pat );
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_instantiations_user_patterns;
    IntStat d_instantiations_auto_gen;
    IntStat d_instantiations_guess;
    IntStat d_instantiations_cbqi_arith;
    IntStat d_instantiations_cbqi_arith_minus;
    IntStat d_instantiations_cbqi_datatypes;
    IntStat d_instantiations_lte;
    IntStat d_instantiation_rounds;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  /** Identify this module */
  std::string identify() const { return "InstEngine"; }
};/* class InstantiationEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
