(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 4))
(assert  (= (_ bv0 1) ((_ extract 0 0) (bvadd (_ bv1 4) (bvnot v0)))) )
(check-sat)
