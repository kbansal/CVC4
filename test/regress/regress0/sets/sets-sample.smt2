(set-logic ALL_SUPPORTED)
(define-sort SetInt () (Set Int))

; Something simple to test parsing
(push 1)
(declare-fun a () (Set Int))
(declare-fun b () (Set Int))
(declare-fun c () (Set Int))
(declare-fun e () Int)
(assert (= a (setenum 5)))
(assert (= c (union a b) ))
(assert (not (= c (intersection a b) )))
(assert (= c (setminus a b) ))
(assert (subset a b))
(assert (in e c))
(assert (in e a))
(assert (in e (intersection a b)))
(check-sat)
(pop 1)

; UF can tell that this is UNSAT (union)
(push 1)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun z () (Set Int))
(assert (= x y))
(assert (not (= (union x z) (union y z))))
(check-sat)
(pop 1)

; UF can tell that this is UNSAT (containment)
(push 1)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)
(assert (= x y))
(assert (= e1 e2))
(assert (in e1 x))
(assert (not (in e2 y)))
(check-sat)
(pop 1)

; UF can tell that this is UNSAT (merge union + containment examples)
(push 1)
(declare-fun x () (Set Int))
(declare-fun y () (Set Int))
(declare-fun z () (Set Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)
(assert (= x y))
(assert (= e1 e2))
(assert (in e1 (union x z)))
(assert (not (in e2 (union y z))))
(check-sat)
(pop 1)
 
(exit) 
(exit)
