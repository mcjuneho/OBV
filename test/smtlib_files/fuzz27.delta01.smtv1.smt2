(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 4))
(assert  (let ((_let_0 (ite (bvslt v0 (_ bv0 4)) (_ bv1 1) (_ bv0 1)))) (distinct (bvneg _let_0) (bvnot _let_0))) )
(check-sat)
