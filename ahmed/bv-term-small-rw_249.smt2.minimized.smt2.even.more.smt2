(set-logic QF_BV)
(declare-fun s () (_ BitVec 2))
(assert (= (bvlshr s s) (bvnot s)))
(check-sat)
(exit)
