(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 4))
(assert  (distinct (_ bv0 1) (bvsub (bvor (bvcomp v0 (_ bv0 4)) (ite (bvslt (_ bv0 4) ((_ sign_extend 3) (ite (bvslt ((_ zero_extend 3) (ite (distinct v0 (_ bv0 4)) (_ bv1 1) (_ bv0 1))) (_ bv0 4)) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1))) )
(check-sat)
