/*********************                                                        */
/*! \file options_handlers.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Custom handlers and predicates for DecisionEngine options
 **
 ** Custom handlers and predicates for DecisionEngine options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__DECISION__OPTIONS_HANDLERS_H
#define __CVC4__DECISION__OPTIONS_HANDLERS_H

#include "decision/decision_mode.h"
#include "main/options.h"

namespace CVC4 {
namespace decision {

static const std::string decisionModeHelp = "\
Decision modes currently supported by the --decision option:\n\
\n\
internal (default)\n\
+ Use the internal decision hueristics of the SAT solver\n\
\n\
justification\n\
+ An ATGP-inspired justification heuristic\n\
\n\
justification-stoponly\n\
+ Use the justification heuristic only to stop early, not for decisions\n\
";

inline DecisionMode stringToDecisionMode(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  options::decisionStopOnly.set(false);

  if(optarg == "internal") {
    return DECISION_STRATEGY_INTERNAL;
  } else if(optarg == "justification") {
    return DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "justification-stoponly") {
    options::decisionStopOnly.set(true);
    return DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "help") {
    puts(decisionModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --decision: `") +
                          optarg + "'.  Try --decision help.");
  }
}

inline DecisionWeightInternal stringToDecisionWeightInternal(std::string option, std::string optarg, SmtEngine* smt) throw(OptionException) {
  static const std::string decisionWeightInternalHelp = "\
Decision weight computation modes currently supported by the\n\
 --decision-weight-internal option:\n\
\n\
off        : use weights as set by theory\n\
max, sum   : auto compute weights of internal nodes from children\n\
usr1       : use polarity and accordingly use max or min\n\
usr2       : usr1 + use activity in conjunction with weights set by theory\n\
act        : override weight of theories, using sat solver activity as weights\n\
act-internal-sum : use sat solver activity only for atoms, sum for internal\
";

  if(optarg == "off") {
    return DECISION_WEIGHT_INTERNAL_OFF;
  } else if(optarg == "max") {
    return DECISION_WEIGHT_INTERNAL_MAX;
  } else if(optarg == "sum") {
    return DECISION_WEIGHT_INTERNAL_SUM;
  } else if(optarg == "usr1") {
    return DECISION_WEIGHT_INTERNAL_USR1;
  } else if(optarg == "usr2") {
    return DECISION_WEIGHT_INTERNAL_USR2;
  } else if(optarg == "act") {
    return DECISION_WEIGHT_ACTIVITY;
  } else if(optarg == "act-internal-sum") {
    return DECISION_WEIGHT_ACTIVITY_INTERNAL_SUM;
  } else if(optarg == "help") {
    puts(decisionWeightInternalHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --decision-weight-internal: `") +
                          optarg + "'.  Try --decision help.");
  }
}

}/* CVC4::decision namespace */
}/* CVC4 namespace */

#endif /* __CVC4__DECISION__OPTIONS_HANDLERS_H */
