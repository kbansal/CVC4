/*********************                                                        */
/*! \file emptyset.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: Morgan Deters
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

#include "cvc4_public.h"

#pragma once

namespace CVC4 {
  // messy; Expr needs EmptySet (because it's the payload of a
  // CONSTANT-kinded expression), and EmptySet needs Expr.
  class CVC4_PUBLIC ConstantSet;
}/* CVC4 namespace */

#include "expr/expr.h"
#include "expr/type.h"
#include "util/finiteset.h"
#include <iostream>

namespace CVC4 {

class CVC4_PUBLIC ConstantSetException : public Exception {
public:
  ConstantSetException(std::string s) throw() : Exception() {
    setMessage(s);
  }
};

typedef ConstantSet EmptySet;

class ConstantSet {

  const SetType d_type;

  std::set<NodeTemplate<true> >* p_elements;

  ConstantSet() { }

public:

  /** Empty set */
  ConstantSet(SetType setType)
    throw (ConstantSetException);

  ConstantSet(SetType setType, const std::set<Expr>& v)
    throw (ConstantSetException);

  ~ConstantSet() throw();

  SetType getType() const { return d_type; }
  size_t getHash() const;

  bool operator==(const ConstantSet& es) const throw();
  bool operator!=(const ConstantSet& es) const throw();
  bool operator<(const ConstantSet& es) const throw();
  bool operator<=(const ConstantSet& es) const throw();
  bool operator>(const ConstantSet& es) const throw();
  bool operator>=(const ConstantSet& es) const throw();

  bool empty() const;
  ConstantSet setunion(const ConstantSet& es) const;
  ConstantSet setintersection(const ConstantSet& es) const;
  ConstantSet setminus(const ConstantSet& es) const;
  bool member(Expr e) const;

  bool member(NodeTemplate<false>* n) const;
  const std::set<NodeTemplate<true> >* getMembers() const;

};/* ConstantSet */

struct CVC4_PUBLIC ConstantSetHashFunction {
  size_t operator()(const ConstantSet& es) const {
    return es.getHash();
  }
};/* struct EmptySetHashFunction */

std::ostream& operator<<(std::ostream& out, const ConstantSet& es) CVC4_PUBLIC;

}/* CVC4 namespace */
