(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 4))
(assert  (let ((_let_0 (bvmul v1 v1))) (distinct _let_0 (bvsub (_ bv0 4) _let_0))) )
(check-sat)
