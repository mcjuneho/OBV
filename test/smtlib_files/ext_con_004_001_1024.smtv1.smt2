(set-option :incremental false)



(set-logic QF_BV)
(declare-fun a () (_ BitVec 1024))
(declare-fun dummy () (_ BitVec 256))
(declare-fun v1 () (_ BitVec 1024))
(declare-fun v2 () (_ BitVec 1024))
(declare-fun v3 () (_ BitVec 1024))
(declare-fun v4 () (_ BitVec 1024))
(assert  (let ((_let_0 ((_ extract 1023 256) a))) (let ((_let_1 ((_ extract 767 0) a))) (and (not (= ((_ extract 767 512) v1) ((_ extract 511 256) v1))) (not (= ((_ extract 767 512) v2) ((_ extract 511 256) v2))) (not (= ((_ extract 767 512) v3) ((_ extract 511 256) v3))) (not (= ((_ extract 767 512) v4) ((_ extract 511 256) v4))) (or (and (= _let_0 (concat ((_ extract 1023 512) v1) dummy)) (= _let_1 (concat dummy ((_ extract 511 0) v1)))) (and (= _let_0 (concat ((_ extract 1023 512) v2) dummy)) (= _let_1 (concat dummy ((_ extract 511 0) v2)))) (and (= _let_0 (concat ((_ extract 1023 512) v3) dummy)) (= _let_1 (concat dummy ((_ extract 511 0) v3)))) (and (= _let_0 (concat ((_ extract 1023 512) v4) dummy)) (= _let_1 (concat dummy ((_ extract 511 0) v4)))))))) )
(check-sat)
