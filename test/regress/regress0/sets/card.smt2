(set-logic QF_UFLIAFS)
(declare-sort E 0)
(declare-fun s () (Set E))
(assert (>= (card s) 5))
(check-sat)
