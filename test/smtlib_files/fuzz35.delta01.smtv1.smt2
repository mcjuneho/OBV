(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 4))
(assert  (let ((_let_0 (bvmul v0 (bvsub (_ bv4 4) (_ bv12 4))))) (bvsgt (bvadd _let_0 _let_0) (_ bv0 4))) )
(check-sat)
