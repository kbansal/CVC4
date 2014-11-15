/*********************                                                        */
/*! \file theory_sets_rewriter.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sets theory rewriter.
 **
 ** Sets theory rewriter.
 **/

#include "theory/sets/theory_sets_rewriter.h"
#include "theory/sets/normal_form.h"

namespace CVC4 {
namespace theory {
namespace sets {

typedef std::set<Node> Elements;
typedef std::hash_map<Node, Elements, NodeHashFunction> SettermElementsMap;

bool checkConstantMembership(TNode elementTerm, TNode setTerm)
{
  Assert(setTerm.getKind() == kind::CONSTANTSET);
  return setTerm.getConst<ConstantSet>().member(&elementTerm);
}

// static
RewriteResponse TheorySetsRewriter::postRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();
  Kind kind = node.getKind();

  if(kind == kind::MEMBER) {

    if(node[0].isConst() && node[1].isConst()) {
      // both are constants
      TNode S = preRewrite(node[1]).node;
      bool isMember = checkConstantMembership(node[0], S);
      return RewriteResponse(REWRITE_DONE, nm->mkConst(isMember));
    }

  } else if(kind == kind::SUBSET) {

    TNode A = node[0];
    TNode B = node[1];
    // rewrite (A subset-or-equal B) as (A union B = B)
    return RewriteResponse(REWRITE_AGAIN_FULL,
                           nm->mkNode(kind::EQUAL,
                                      nm->mkNode(kind::UNION, A, B),
                                      B) );

  } else if(kind == kind::EQUAL) {

    //rewrite: t = t with true (t term)
    //rewrite: c = c' with c different from c' false (c, c' constants)
    //otherwise: sort them
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning true" << std::endl;
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
    else if (node[0].isConst() && node[1].isConst()) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning false" << std::endl;
      return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
    }
    else if (node[0] > node[1]) {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }

  } else if(kind == kind::UNION ||
	    kind == kind::INTERSECTION ||
	    kind == kind::SETMINUS) {

    bool leftConstant = (node[0].getKind() == kind::CONSTANTSET);
    bool rightConstant = (node[1].getKind() == kind::CONSTANTSET);

    if(leftConstant && rightConstant) {

      ConstantSet cs0 = node[0].getConst<ConstantSet>();
      ConstantSet cs1 = node[1].getConst<ConstantSet>();
      if(kind == kind::UNION) {
	return RewriteResponse(REWRITE_DONE, nm->mkConst(cs0.setunion(cs1)));
      } else if(kind == kind::INTERSECTION) {
	return RewriteResponse(REWRITE_DONE, nm->mkConst(cs0.setintersection(cs1)));
      } else if(kind == kind::SETMINUS) {
	return RewriteResponse(REWRITE_DONE, nm->mkConst(cs0.setminus(cs1)));
      } else { Unhandled(); }


    } else if(leftConstant && node[0].getConst<ConstantSet>().empty() ) {

      // left side emptyset
      if(kind == kind::UNION) {
	return RewriteResponse(REWRITE_DONE, node[1]);
      } else if(kind == kind::INTERSECTION) {
	return RewriteResponse(REWRITE_DONE, node[0]);
      } else if(kind == kind::SETMINUS) {
	return RewriteResponse(REWRITE_DONE, node[0]);
      } else { Unhandled(); }

    } else if(rightConstant && node[1].getConst<ConstantSet>().empty() ) {

      // right side empty
      if(kind == kind::UNION) {
	return RewriteResponse(REWRITE_DONE, node[0]);
      } else if(kind == kind::INTERSECTION) {
	return RewriteResponse(REWRITE_DONE, node[1]);
      } else if(kind == kind::SETMINUS) {
	return RewriteResponse(REWRITE_DONE, node[0]);
      } else { Unhandled(); }

    } else if(node[0] > node[1]) {

      return RewriteResponse(REWRITE_DONE, nm->mkNode(kind, node[1], node[0]));

    }

  } else if(kind == kind::SINGLETON) {

    if(node[0].isConst()) {
      std::set<Expr> s;
      s.insert(node[0].toExpr());
      ConstantSet cs(node.getType().toType(), s);
      return RewriteResponse(REWRITE_DONE, nm->mkConst(cs));
    }

  } else if(kind == kind::CONSTANTSET) {

    // Do nothing

  } else  {
    Unhandled();
  }

  return RewriteResponse(REWRITE_DONE, node);
  // This default implementation
  // switch(kind) {

  // case kind::MEMBER: {
  //   break;
  // }//kind::MEMBER

  // case kind::SUBSET: {
  // }//kind::SUBSET

  // case kind::EQUAL:
  // case kind::IFF: {
  // }//kind::IFF

  // case kind::SETMINUS: {
  //   if(node[0] == node[1]) {
  //     Node newNode = nm->mkConst(EmptySet(nm->toType(node[0].getType())));
  //     Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
  //     return RewriteResponse(REWRITE_DONE, newNode);
  //   } else if(node[0].getKind() == kind::EMPTYSET ||
  //             node[1].getKind() == kind::EMPTYSET) {
  //     Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
  //     return RewriteResponse(REWRITE_DONE, node[0]);
  //   } else if(node[0].isConst() && node[1].isConst()) {
  //     Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
  //   }
  //   break;
  // }//kind::INTERSECION

  // case kind::INTERSECTION: {
  //   if(node[0] == node[1]) {
  //     Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
  //     return RewriteResponse(REWRITE_DONE, node[0]);
  //   } else if(node[0].getKind() == kind::EMPTYSET) {
  //     return RewriteResponse(REWRITE_DONE, node[0]);
  //   } else if(node[1].getKind() == kind::EMPTYSET) {
  //     return RewriteResponse(REWRITE_DONE, node[1]);
  //   } else if (node[0] > node[1]) {
  //     Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
  //     Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
  //     return RewriteResponse(REWRITE_DONE, newNode);
  //   }
  //   break;
  // }//kind::INTERSECION

  // case kind::UNION: {
  //   if(node[0] == node[1]) {
  //     Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
  //     return RewriteResponse(REWRITE_DONE, node[0]);
  //   } else if(node[0].getKind() == kind::EMPTYSET) {
  //     return RewriteResponse(REWRITE_DONE, node[1]);
  //   } else if(node[1].getKind() == kind::EMPTYSET) {
  //     return RewriteResponse(REWRITE_DONE, node[0]);
  //   } else if (node[0] > node[1]) {
  //     Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
  //     Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
  //     return RewriteResponse(REWRITE_DONE, newNode);
  //   }
  //   break;
  // }//kind::UNION

  // default:
  //   break;
  // }//switch(node.getKind())

}

// const Elements& collectConstantElements(TNode setterm, SettermElementsMap& settermElementsMap) {
//   SettermElementsMap::const_iterator it = settermElementsMap.find(setterm);
//   if(it == settermElementsMap.end() ) {

//     Kind k = setterm.getKind();
//     unsigned numChildren = setterm.getNumChildren();
//     Elements cur;
//     if(numChildren == 2) {
//       const Elements& left = collectConstantElements(setterm[0], settermElementsMap);
//       const Elements& right = collectConstantElements(setterm[1], settermElementsMap);
//       switch(k) {
//       case kind::UNION:
//         if(left.size() >= right.size()) {
//           cur = left; cur.insert(right.begin(), right.end());
//         } else {
//           cur = right; cur.insert(left.begin(), left.end());
//         }
//         break;
//       case kind::INTERSECTION:
//         std::set_intersection(left.begin(), left.end(), right.begin(), right.end(),
//                               std::inserter(cur, cur.begin()) );
//         break;
//       case kind::SETMINUS:
//         std::set_difference(left.begin(), left.end(), right.begin(), right.end(),
//                             std::inserter(cur, cur.begin()) );
//         break;
//       default:
//         Unhandled();
//       }
//     } else {
//       switch(k) {
//       case kind::EMPTYSET:
//         /* assign emptyset, which is default */
//         break;
//       case kind::SINGLETON:
//         Assert(setterm[0].isConst());
//         cur.insert(TheorySetsRewriter::preRewrite(setterm[0]).node);
//         break;
//       default:
//         Unhandled();
//       }
//     }
//     Debug("sets-rewrite-constant") << "[sets-rewrite-constant] "<< setterm << " " << setterm.getId() << std::endl;

//     it = settermElementsMap.insert(SettermElementsMap::value_type(setterm, cur)).first;
//   }
//   return it->second;
// }


// static
RewriteResponse TheorySetsRewriter::preRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();

  // do nothing
  if(node.getKind() == kind::EQUAL && node[0] == node[1])
    return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
  // Further optimization, if constants but differing ones

  if(node.getKind() == kind::INSERT) {
    Node insertedElements = nm->mkNode(kind::SINGLETON, node[0]);
    size_t setNodeIndex =  node.getNumChildren()-1;
    for(size_t i = 1; i < setNodeIndex; ++i) {
      insertedElements = nm->mkNode(kind::UNION, insertedElements, nm->mkNode(kind::SINGLETON, node[i]));
    }
    return RewriteResponse(REWRITE_AGAIN, nm->mkNode(kind::UNION, insertedElements, node[setNodeIndex]));
  }//kind::INSERT

  // if(node.getType().isSet() && node.isConst()) {
  //   //rewrite set to normal form
  //   SettermElementsMap setTermElementsMap;   // cache
  //   const Elements& elements = collectConstantElements(node, setTermElementsMap);
  //   RewriteResponse response(REWRITE_DONE, NormalForm::elementsToSet(elements, node.getType()));
  //   Debug("sets-rewrite-constant") << "[sets-rewrite-constant] Rewriting " << node << std::endl
  //                                  << "[sets-rewrite-constant]        to " << response.node << std::endl;
  //   return response;
  // }

  return RewriteResponse(REWRITE_DONE, node);
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
