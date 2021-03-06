/*********************                                                        */
/*! \file bv_to_bool.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 **
 ** Preprocessing pass that lifts bit-vectors of size 1 to booleans. 
 **/


#include "util/node_visitor.h"
#include "theory/bv/bv_to_bool.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

BvToBoolPreprocessor::BvToBoolPreprocessor()
  : d_liftCache()
  , d_boolCache()
  , d_one(utils::mkConst(BitVector(1, 1u)))
  , d_zero(utils::mkConst(BitVector(1, 0u)))
  , d_statistics()
{}

void BvToBoolPreprocessor::addToLiftCache(TNode term, Node new_term) {
  Assert (new_term != Node()); 
  Assert (!hasLiftCache(term));
  Assert (term.getType() == new_term.getType());
  d_liftCache[term] = new_term; 
}

Node BvToBoolPreprocessor::getLiftCache(TNode term) const {
  Assert(hasLiftCache(term)); 
  return d_liftCache.find(term)->second; 
}

bool BvToBoolPreprocessor::hasLiftCache(TNode term) const {
  return d_liftCache.find(term) != d_liftCache.end(); 
}

void BvToBoolPreprocessor::addToBoolCache(TNode term, Node new_term) {
  Assert (new_term != Node()); 
  Assert (!hasBoolCache(term));
  Assert (utils::getSize(term) == 1);
  Assert (new_term.getType().isBoolean());
  d_boolCache[term] = new_term; 
}

Node BvToBoolPreprocessor::getBoolCache(TNode term) const {
  Assert(hasBoolCache(term)); 
  return d_boolCache.find(term)->second; 
}

bool BvToBoolPreprocessor::hasBoolCache(TNode term) const {
  return d_boolCache.find(term) != d_boolCache.end(); 
}
bool BvToBoolPreprocessor::isConvertibleBvAtom(TNode node) {
  Kind kind = node.getKind();
  return (kind == kind::EQUAL &&
          node[0].getType().isBitVector() &&
          node[0].getType().getBitVectorSize() == 1 &&
          node[1].getType().isBitVector() &&
          node[1].getType().getBitVectorSize() == 1 &&
          node[0].getKind() != kind::BITVECTOR_EXTRACT &&
          node[1].getKind() != kind::BITVECTOR_EXTRACT); 
}

bool BvToBoolPreprocessor::isConvertibleBvTerm(TNode node) {
  if (!node.getType().isBitVector() ||
      node.getType().getBitVectorSize() != 1)
    return false;

  Kind kind = node.getKind();
  
  if (kind == kind::CONST_BITVECTOR ||
      kind == kind::ITE ||
      kind == kind::BITVECTOR_AND ||
      kind == kind::BITVECTOR_OR ||
      kind == kind::BITVECTOR_NOT ||
      kind == kind::BITVECTOR_XOR ||
      kind == kind::BITVECTOR_COMP) {
    return true; 
  }

  return false; 
}

Node BvToBoolPreprocessor::convertBvAtom(TNode node) {
  Assert (node.getType().isBoolean() &&
          node.getKind() == kind::EQUAL);
  Assert (utils::getSize(node[0]) == 1);
  Assert (utils::getSize(node[1]) == 1);
  Node a = convertBvTerm(node[0]);
  Node b = convertBvTerm(node[1]);
  Node result = utils::mkNode(kind::IFF, a, b); 
  Debug("bv-to-bool") << "BvToBoolPreprocessor::convertBvAtom " << node <<" => " << result << "\n";

  ++(d_statistics.d_numAtomsLifted);
  return result;
}

Node BvToBoolPreprocessor::convertBvTerm(TNode node) {
  Assert (node.getType().isBitVector() &&
          node.getType().getBitVectorSize() == 1);

  if (hasBoolCache(node))
    return getBoolCache(node);
  
  if (!isConvertibleBvTerm(node)) {
    ++(d_statistics.d_numTermsForcedLifted);
    Node result = utils::mkNode(kind::EQUAL, node, d_one);
    addToBoolCache(node, result);
    Debug("bv-to-bool") << "BvToBoolPreprocessor::convertBvTerm " << node <<" => " << result << "\n"; 
    return result;
  }

  if (node.getNumChildren() == 0) {
    Assert (node.getKind() == kind::CONST_BITVECTOR);
    Node result = node == d_one ? utils::mkTrue() : utils::mkFalse();
    // addToCache(node, result);
    Debug("bv-to-bool") << "BvToBoolPreprocessor::convertBvTerm " << node <<" => " << result << "\n"; 
    return result; 
  }

  ++(d_statistics.d_numTermsLifted);
  
  Kind kind = node.getKind();
  if (kind == kind::ITE) {
    Node cond = liftNode(node[0]);
    Node true_branch = convertBvTerm(node[1]);
    Node false_branch = convertBvTerm(node[2]);
    Node result = utils::mkNode(kind::ITE, cond, true_branch, false_branch);
    addToBoolCache(node, result);
    Debug("bv-to-bool") << "BvToBoolPreprocessor::convertBvTerm " << node <<" => " << result << "\n"; 
    return result; 
  }

  Kind new_kind;
  // special case for XOR as it has to be binary
  // while BITVECTOR_XOR can be n-ary
  if (kind == kind::BITVECTOR_XOR) {
    new_kind = kind::XOR;
    Node result = convertBvTerm(node[0]);
    for (unsigned i = 1; i < node.getNumChildren(); ++i) {
      Node converted = convertBvTerm(node[i]);
      result = utils::mkNode(kind::XOR, result, converted); 
    }
    Debug("bv-to-bool") << "BvToBoolPreprocessor::convertBvTerm " << node <<" => " << result << "\n"; 
    return result; 
  }

  if (kind == kind::BITVECTOR_COMP) {
    Node result = utils::mkNode(kind::EQUAL, node[0], node[1]);
    addToBoolCache(node, result);
    Debug("bv-to-bool") << "BvToBoolPreprocessor::convertBvTerm " << node <<" => " << result << "\n"; 
    return result; 
  }

  switch(kind) {
  case kind::BITVECTOR_OR:
    new_kind = kind::OR;
    break;
  case kind::BITVECTOR_AND:
    new_kind = kind::AND;
    break;
  case kind::BITVECTOR_XOR:
    new_kind = kind::XOR;
    break;
  case kind::BITVECTOR_NOT:
    new_kind = kind::NOT;
    break;
  default:
    Unhandled(); 
  }

  NodeBuilder<> builder(new_kind);
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    builder << convertBvTerm(node[i]); 
  }
  
  Node result = builder;
  addToBoolCache(node, result);
  Debug("bv-to-bool") << "BvToBoolPreprocessor::convertBvTerm " << node <<" => " << result << "\n"; 
  return result; 
}



Node BvToBoolPreprocessor::liftNode(TNode current) {
  Node result;
  
  if (hasLiftCache(current)) {
    result = getLiftCache(current); 
  }else if (isConvertibleBvAtom(current)) {
    result = convertBvAtom(current);
    addToLiftCache(current, result);
  } else {
    if (current.getNumChildren() == 0) {
      result = current;
    } else {
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        Node converted = liftNode(current[i]);
        Assert (converted.getType() == current[i].getType()); 
        builder << converted; 
      }
      result = builder;
      addToLiftCache(current, result);
    }
  }
  Assert (result != Node());
  Assert(result.getType() == current.getType());
  Debug("bv-to-bool") << "BvToBoolPreprocessor::liftNode " << current << " => \n" << result << "\n"; 
  return result; 
}


void BvToBoolPreprocessor::liftBvToBool(const std::vector<Node>& assertions, std::vector<Node>& new_assertions) {
  for (unsigned i = 0; i < assertions.size(); ++i) {
    Node new_assertion = liftNode(assertions[i]);
    new_assertions.push_back(new_assertion);
    Trace("bv-to-bool") << "  " << assertions[i] <<" => " << new_assertions[i] <<"\n"; 
  }
}

BvToBoolPreprocessor::Statistics::Statistics()
  : d_numTermsLifted("theory::bv::BvToBoolPreprocess::NumberOfTermsLifted", 0)
  , d_numAtomsLifted("theory::bv::BvToBoolPreprocess::NumberOfAtomsLifted", 0)
  , d_numTermsForcedLifted("theory::bv::BvToBoolPreprocess::NumberOfTermsForcedLifted", 0)
{
  StatisticsRegistry::registerStat(&d_numTermsLifted);
  StatisticsRegistry::registerStat(&d_numAtomsLifted);
  StatisticsRegistry::registerStat(&d_numTermsForcedLifted);
}

BvToBoolPreprocessor::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numTermsLifted);
  StatisticsRegistry::unregisterStat(&d_numAtomsLifted);
  StatisticsRegistry::unregisterStat(&d_numTermsForcedLifted);
}
