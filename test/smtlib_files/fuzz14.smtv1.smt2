(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v2 () (_ BitVec 13))
(declare-fun v1 () (_ BitVec 2))
(assert  (let ((_let_0 (ite (bvslt (_ bv0 13) v2) (_ bv1 1) (_ bv0 1)))) (let ((_let_1 (ite (= (_ bv1 1) (ite (bvsge (_ bv0 2) v1) (_ bv1 1) (_ bv0 1))) (bvneg _let_0) _let_0))) (let ((_let_2 (bvashr v2 v2))) (let ((_let_3 (ite (= (_ bv0 13) (bvshl v2 _let_2)) (= _let_2 (bvsub (_ bv1 13) v2)) (= (_ bv1 10) ((_ sign_extend 9) _let_1))))) (=> (not (and (= v2 ((_ zero_extend 12) _let_1)) (= (_ bv1 1) _let_0))) (ite _let_3 (=> (= _let_1 (ite (bvult (bvneg _let_0) (_ bv1 1)) (_ bv1 1) (_ bv0 1))) (= (_ bv0 4) ((_ sign_extend 3) _let_1))) _let_3)))))) )
(check-sat)
