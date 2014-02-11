(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-fun S () (Set Int))
(declare-fun T () (Set Int))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (in y S))
(assert (not (in x (union S T))))
(assert (= x y))
(check-sat)
