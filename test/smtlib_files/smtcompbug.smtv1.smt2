(set-option :incremental false)


(set-logic QF_BV)
(declare-fun x781 () (_ BitVec 32))
(declare-fun x803 () (_ BitVec 8))
(declare-fun x804 () (_ BitVec 8))
(declare-fun x791 () (_ BitVec 8))
(assert  (and (= x804 (bvxor (bvxor ((_ extract 7 0) (bvadd (_ bv1 32) x781)) x791) x803)) (= (bvnot ((_ extract 0 0) x804)) (_ bv0 1)) (= x781 (_ bv0 32))) )
(check-sat)
