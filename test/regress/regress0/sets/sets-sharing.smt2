(set-logic ALL_SUPPORTED)

(declare-fun S () (Set Int))
(declare-fun x () Int)

(assert (in (+ 5 x) S))
(assert (not (in 9 S)))
(assert (= x 4))

(check-sat)
