(set-logic QF_ALL_SUPPORTED)
(assert (= (as emptyset (Set Int)) (setenum 5)))
(check-sat)
