(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 4))
(assert  (bvsge ((_ extract 3 0) (bvmul (_ bv1 4) v0)) (_ bv0 4)) )
(check-sat)
