(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 4))
(assert  (= (_ bv1 1) ((_ extract 0 0) (bvsub (bvnot v1) (_ bv1 4)))) )
(check-sat)
