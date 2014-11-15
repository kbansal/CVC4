/*********************                                                        */
/*! \file emptyset.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/emptyset.h"
#include "expr/node.h"
#include <iostream>

using namespace std;

namespace CVC4 {

typedef std::set<Node> Elements;

ConstantSet::ConstantSet(SetType setType)
  throw (ConstantSetException):
  d_type(setType)
  , p_elements(new Elements)
{
}


ConstantSet::ConstantSet(SetType setType, const std::set<Expr>& elements)
  throw (ConstantSetException):
  d_type(setType)
  , p_elements(new Elements(elements.begin(), elements.end()))
{
  typeof(elements.begin()) it = elements.begin();
  while( ++it != elements.end() ) {
    if( !(*it).isConst() ) {
      throw ConstantSetException("non-constant elements not allowed");
    }
  }
}

ConstantSet::~ConstantSet() throw() {
  delete p_elements;
}

size_t ConstantSet::getHash() const {
  size_t h = 0;
  for(typeof(p_elements->begin()) it = p_elements->begin();
      it != p_elements->end(); ++it) {
    h ^= (*it).getId() + 0x9e3779b9 + (h << 6) + (h >> 2);
  }
  return h;
}


bool ConstantSet::operator==(const ConstantSet& es) const throw() {
  return d_type == es.d_type && p_elements == es.p_elements;
}
bool ConstantSet::operator!=(const ConstantSet& es) const throw() {
  return !(*this == es);
}
bool ConstantSet::operator<(const ConstantSet& es) const throw() {
  return d_type < es.d_type || (d_type == es.d_type && p_elements < es.p_elements);
}
bool ConstantSet::operator<=(const ConstantSet& es) const throw() {
  return d_type < es.d_type || (d_type == es.d_type && p_elements <= es.p_elements);
}
bool ConstantSet::operator>(const ConstantSet& es) const throw() {
  return !(*this <= es);
}
bool ConstantSet::operator>=(const ConstantSet& es) const throw() {
  return !(*this < es);
}


bool ConstantSet::empty() const {
  return p_elements->size();
}

ConstantSet ConstantSet::setunion(const ConstantSet& es) const {
  ConstantSet ret(d_type);
  if(d_type != es.d_type) {
    throw ConstantSetException("operating on sets of different types");
  }
  std::set_union(p_elements->begin(), p_elements->end(),
                 es.p_elements->begin(), es.p_elements->end(),
                 std::inserter(*(ret.p_elements), ret.p_elements->begin()));
  return ret;
}

ConstantSet ConstantSet::setintersection(const ConstantSet& es) const {
  ConstantSet ret(d_type);
  if(d_type != es.d_type) {
    throw ConstantSetException("operating on sets of different types");
  }
  std::set_intersection(p_elements->begin(), p_elements->end(),
                 es.p_elements->begin(), es.p_elements->end(),
                 std::inserter(*(ret.p_elements), ret.p_elements->begin()));
  return ret;
}

ConstantSet ConstantSet::setminus(const ConstantSet& es) const {
  ConstantSet ret(d_type);
  if(d_type != es.d_type) {
    throw ConstantSetException("operating on sets of different types");
  }
  std::set_difference(p_elements->begin(), p_elements->end(),
                 es.p_elements->begin(), es.p_elements->end(),
                 std::inserter(*(ret.p_elements), ret.p_elements->begin()));
  return ret;
}

bool ConstantSet::member(Expr e) const {
  Node n = Node::fromExpr(e);
  TNode tn = n;
  return member(&tn);
}
bool ConstantSet::member(NodeTemplate<false>* n) const {
  return p_elements->find(*n) != p_elements->end();
}

const std::set<NodeTemplate<true> >* ConstantSet::getMembers() const {
  return p_elements;
}


std::ostream& operator<<(std::ostream& out, const ConstantSet& asa) {
  return out << "constantset(" << asa.getType() << ": ...)";
}


}/* CVC4 namespace */
