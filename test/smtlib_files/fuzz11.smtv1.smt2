(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 11))
(assert  (= v0 ((_ zero_extend 10) (ite (bvsge (_ bv0 16) ((_ zero_extend 5) v0)) (_ bv1 1) (_ bv0 1)))) )
(check-sat)
