#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_REWRITER_H
#define __CVC4__THEORY__SETS__THEORY_SETS_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsRewriter {
public:

  /**
   * Rewrite a node into the normal form for the theory of sets.
   * Called in post-order (really reverse-topological order) when
   * traversing the expression DAG during rewriting.  This is the
   * main function of the rewriter, and because of the ordering,
   * it can assume its children are all rewritten already.
   *
   * This function can return one of three rewrite response codes
   * along with the rewritten node:
   *
   *   REWRITE_DONE indicates that no more rewriting is needed.
   *   REWRITE_AGAIN means that the top-level expression should be
   *     rewritten again, but that its children are in final form.
   *   REWRITE_AGAIN_FULL means that the entire returned expression
   *     should be rewritten again (top-down with preRewrite(), then
   *     bottom-up with postRewrite()).
   *
   * Even if this function returns REWRITE_DONE, if the returned
   * expression belongs to a different theory, it will be fully
   * rewritten by that theory's rewriter.
   */
  static RewriteResponse postRewrite(TNode node) {
    NodeManager* nm = NodeManager::currentNM();

    switch(node.getKind()) {

    case kind::SUBSET: {
      // rewrite (A subset-or-equal B) as (A union B = B) 
      TNode A = node[0];
      TNode B = node[1];
      return RewriteResponse(REWRITE_AGAIN,
                             nm->mkNode(kind::EQUAL,
                                        nm->mkNode(kind::UNION, A, B),
                                        B) );
    }//kind::SUBSET

    case kind::EQUAL:
    case kind::IFF: {
      //rewrite: t = t with true (t term)
      //rewrite: c = c' with c different from c' false (c, c' constants)
      //otherwise: sort them
      if(node[0] == node[1]) {
        Trace("arrays-postrewrite") << "Arrays::postRewrite returning true" << std::endl;
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }
      else if (node[0].isConst() && node[1].isConst()) {
        Trace("arrays-postrewrite") << "Arrays::postRewrite returning false" << std::endl;
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
      if (node[0] > node[1]) {
        Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
        Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      break;
    }
    default:
      break;

    }//switch(node.getKind())
  // This default implementation
  return RewriteResponse(REWRITE_DONE, node);
  }

  /**
   * Rewrite a node into the normal form for the theory of sets
   * in pre-order (really topological order)---meaning that the
   * children may not be in the normal form.  This is an optimization
   * for theories with cancelling terms (e.g., 0 * (big-nasty-expression)
   * in arithmetic rewrites to 0 without the need to look at the big
   * nasty expression).  Since it's only an optimization, the
   * implementation here can do nothing.
   */
  static RewriteResponse preRewrite(TNode node) {
    NodeManager* nm = NodeManager::currentNM();

    // do nothing
    if(node.getKind() == kind::EQUAL && node[0] == node[1])
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    // Further optimization, if constants but differing ones

    return RewriteResponse(REWRITE_DONE, node);
  }

  /**
   * Rewrite an equality, in case special handling is required.
   */
  static Node rewriteEquality(TNode equality) {
    // often this will suffice
    return postRewrite(equality).node;
  }

  /**
   * Initialize the rewriter.
   */
  static inline void init() {
    // nothing to do
  }

  /**
   * Shut down the rewriter.
   */
  static inline void shutdown() {
    // nothing to do
  }

};/* class TheorySetsRewriter */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_REWRITER_H */
