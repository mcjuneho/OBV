(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 9))
(assert  (let ((_let_0 (ite (bvsgt (_ bv0 6) ((_ sign_extend 5) (ite (bvult (_ bv0 9) v1) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (= _let_0 (bvcomp v1 ((_ sign_extend 8) _let_0)))) )
(check-sat)
