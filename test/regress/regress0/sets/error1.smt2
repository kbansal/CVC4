(set-logic QF_ALL_SUPPORTED)
(define-sort Elt () Int)
(define-sort mySet () (Set Elt ))
(define-fun smt_set_emp () mySet (as emptyset mySet))
(define-fun smt_set_mem ((x Elt) (s mySet)) Bool (in x s))
(define-fun smt_set_add ((s mySet) (x Elt)) mySet (union s (setenum x)))
(define-fun smt_set_cup ((s1 mySet) (s2 mySet)) mySet (union s1 s2))
(define-fun smt_set_cap ((s1 mySet) (s2 mySet)) mySet (intersection s1 s2))
(define-fun smt_set_dif ((s1 mySet) (s2 mySet)) mySet (setminus s1 s2))
(define-fun smt_set_sub ((s1 mySet) (s2 mySet)) Bool (subseteq s1 s2))
;; (declare-fun z3f97 (Int) mySet)

(declare-fun A () mySet)			;236
(declare-fun B () mySet)			;251
(declare-fun C () mySet)			;235
(declare-fun D () mySet)			;235
(declare-fun E () mySet)			;203

(declare-fun x () Int)
;; (declare-fun z3v203 () Int)
;; (declare-fun z3v204 () Int)
;; (declare-fun z3v235 () Int)
;; (declare-fun z3v236 () Int)
;; (declare-fun z3v251 () Int)

(assert (= A (union D C)))
(assert (not (= A (union E A))))
;; (assert (= B (union D C)))

(check-sat)
