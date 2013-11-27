(set-logic QF_ALL_SUPPORTED)

(declare-fun A () (Set Int))
(declare-fun C () (Set Int))
(declare-fun D () (Set Int))
(declare-fun E () (Set Int))

(assert (= A (union D C)))
(assert (not (= A (union E A))))

(check-sat)
