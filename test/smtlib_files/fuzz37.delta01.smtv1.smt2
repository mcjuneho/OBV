(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 4))
(assert  (let ((_let_0 (bvmul v1 ((_ zero_extend 3) (ite (bvugt (_ bv1 4) v1) (_ bv1 1) (_ bv0 1)))))) (= _let_0 (bvsub (_ bv0 4) _let_0))) )
(check-sat)
