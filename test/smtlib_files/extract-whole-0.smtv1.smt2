(set-option :incremental false)

(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(assert  (not (= (concat (concat (concat (concat (concat (concat (_ bv0 1) ((_ extract 31 31) x)) ((_ extract 30 20) x)) ((_ extract 19 10) x)) ((_ extract 9 1) x)) ((_ extract 0 0) x)) (_ bv0 1)) (concat (concat (_ bv0 1) x) (_ bv0 1)))) )
(check-sat)
