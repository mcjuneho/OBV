(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v1 () (_ BitVec 2))
(assert  (let ((_let_0 ((_ sign_extend 1) (ite (bvugt (bvcomp v1 (_ bv1 2)) (_ bv0 1)) (_ bv1 1) (_ bv0 1))))) (ite (= (_ bv0 8) (concat (_ bv0 2) (concat (ite (= (_ bv0 5) ((_ sign_extend 3) v1)) (_ bv1 1) (_ bv0 1)) (_ bv0 5)))) false (ite (= (_ bv0 4) ((_ sign_extend 2) _let_0)) true (= (_ bv0 16) ((_ zero_extend 15) (ite (distinct (_ bv0 3) ((_ zero_extend 2) (ite (bvsle (_ bv0 2) _let_0) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1))))))) )
(check-sat)
