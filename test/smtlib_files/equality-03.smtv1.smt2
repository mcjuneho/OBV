(set-option :incremental false)




(set-logic QF_BV)
(declare-fun x0 () (_ BitVec 32))
(declare-fun x1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 32))
(declare-fun y0 () (_ BitVec 32))
(declare-fun y1 () (_ BitVec 32))
(declare-fun y2 () (_ BitVec 32))
(declare-fun a0 () (_ BitVec 32))
(declare-fun a1 () (_ BitVec 32))
(declare-fun a2 () (_ BitVec 32))
(declare-fun a3 () (_ BitVec 32))
(assert (xor (and (= a0 x0) (= x0 a1)) (and (= a0 y0) (= y0 a1))))
(assert (xor (and (= a1 x1) (= x1 a2)) (and (= a1 y1) (= y1 a2))))
(assert (xor (and (= a2 x2) (= x2 a3)) (and (= a2 y2) (= y2 a3))))
(assert  (not (= a0 a3)) )
(check-sat)
