(benchmark fuzzsmt
:logic QF_UFLRA
:extrapreds ((p0 Real Real))
:extrafuns ((v0 Real))
:status sat
:formula
(let (?n1 6)
(let (?n2 (~ ?n1))
(flet ($n3 (p0 ?n2 ?n1))
(let (?n4 1)
(let (?n5 0)
(let (?n6 (ite $n3 ?n4 ?n5))
(let (?n7 (+ ?n2 ?n6))
(flet ($n8 (p0 ?n1 ?n7))
(let (?n9 7)
(flet ($n10 (p0 ?n9 ?n1))
(let (?n11 (ite $n10 ?n4 ?n5))
(flet ($n12 (distinct ?n1 ?n11))
(flet ($n13 (p0 v0 ?n1))
(let (?n14 (ite $n13 ?n4 ?n5))
(flet ($n15 (<= ?n14 ?n2))
(let (?n16 (+ ?n7 ?n7))
(let (?n17 (ite $n15 ?n1 ?n16))
(let (?n18 (ite $n12 ?n17 v0))
(flet ($n19 (p0 ?n18 ?n1))
(flet ($n20 (implies $n8 $n19))
(flet ($n21 (p0 ?n16 v0))
(flet ($n22 false)
(flet ($n23 (if_then_else $n20 $n21 $n22))
$n23
))))))))))))))))))))))))
