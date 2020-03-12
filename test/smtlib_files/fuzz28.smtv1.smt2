(set-option :incremental false)

(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 4))
(declare-fun v1 () (_ BitVec 4))
(declare-fun v2 () (_ BitVec 4))
(declare-fun v3 () (_ BitVec 4))
(assert  (let ((_let_0 (bvneg v0))) (let ((_let_1 ((_ rotate_left 0) v0))) (let ((_let_2 (bvxnor v3 (_ bv5 4)))) (let ((_let_3 (bvnand v0 _let_1))) (let ((_let_4 (bvcomp _let_1 (bvnand (_ bv5 4) _let_2)))) (let ((_let_5 ((_ sign_extend 3) (ite (bvsgt (_ bv13 4) (_ bv14 4)) (_ bv1 1) (_ bv0 1))))) (let ((_let_6 (bvadd _let_3 ((_ zero_extend 3) _let_4)))) (let ((_let_7 ((_ zero_extend 3) (ite (bvslt v0 (_ bv12 4)) (_ bv1 1) (_ bv0 1))))) (let ((_let_8 ((_ zero_extend 0) (ite (bvsgt (_ bv13 4) ((_ sign_extend 3) (ite (bvslt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1))))) (let ((_let_9 ((_ extract 0 0) (bvnand (_ bv5 4) _let_2)))) (let ((_let_10 ((_ zero_extend 3) (ite (bvsgt (_ bv13 4) (_ bv14 4)) (_ bv1 1) (_ bv0 1))))) (let ((_let_11 (ite (= _let_10 _let_6) (_ bv1 1) (_ bv0 1)))) (let ((_let_12 ((_ rotate_right 1) _let_0))) (let ((_let_13 (bvmul _let_1 v0))) (let ((_let_14 (bvshl (_ bv5 4) ((_ sign_extend 3) _let_11)))) (let ((_let_15 ((_ zero_extend 3) _let_9))) (let ((_let_16 (ite (bvuge (bvnand (_ bv5 4) _let_2) _let_15) (_ bv1 1) (_ bv0 1)))) (let ((_let_17 ((_ rotate_left 0) _let_6))) (let ((_let_18 (bvshl v3 (bvnand (_ bv5 4) _let_2)))) (let ((_let_19 (ite (bvsgt _let_12 (_ bv13 4)) (_ bv1 1) (_ bv0 1)))) (let ((_let_20 ((_ sign_extend 3) _let_8))) (let ((_let_21 (ite (bvsle v1 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1)))) (let ((_let_22 ((_ rotate_right 1) _let_13))) (let ((_let_23 (ite (bvsge _let_5 _let_1) (_ bv1 1) (_ bv0 1)))) (let ((_let_24 (bvxor (bvnot v0) (bvadd _let_12 _let_20)))) (let ((_let_25 ((_ zero_extend 2) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))))) (let ((_let_26 (ite (bvslt (bvadd _let_3 _let_2) ((_ zero_extend 3) _let_4)) (_ bv1 1) (_ bv0 1)))) (let ((_let_27 (bvnand _let_8 _let_11))) (let ((_let_28 (bvand ((_ sign_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))) (bvlshr (_ bv13 4) _let_7)))) (let ((_let_29 (bvnor (_ bv12 4) _let_17))) (let ((_let_30 ((_ repeat 2) _let_23))) (let ((_let_31 (bvxnor v0 (bvmul ((_ sign_extend 3) _let_4) (bvadd _let_3 _let_2))))) (let ((_let_32 ((_ sign_extend 3) _let_23))) (let ((_let_33 (ite (bvslt _let_13 _let_32) (_ bv1 1) (_ bv0 1)))) (let ((_let_34 (bvashr (_ bv13 4) ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))))) (let ((_let_35 (bvnor ((_ rotate_left 1) (bvadd (bvnot v0) (_ bv13 4))) (bvnor (_ bv5 4) (bvxnor ((_ sign_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4))))))) (let ((_let_36 (bvlshr (ite (= (bvnand (_ bv5 4) _let_2) _let_0) (_ bv1 1) (_ bv0 1)) _let_27))) (let ((_let_37 (bvult _let_9 _let_19))) (let ((_let_38 (bvsgt ((_ zero_extend 3) _let_4) ((_ sign_extend 3) _let_11)))) (let ((_let_39 (bvslt _let_12 ((_ sign_extend 3) _let_4)))) (let ((_let_40 (= ((_ sign_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))) ((_ zero_extend 3) _let_4)))) (let ((_let_41 ((_ sign_extend 3) (bvcomp (bvnot v0) (_ bv5 4))))) (let ((_let_42 (bvslt ((_ repeat 1) (_ bv14 4)) ((_ zero_extend 0) _let_31)))) (let ((_let_43 (bvult _let_18 _let_17))) (let ((_let_44 ((_ zero_extend 3) (ite (bvule (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)) _let_26) (_ bv1 1) (_ bv0 1))))) (let ((_let_45 ((_ zero_extend 3) _let_21))) (let ((_let_46 (bvuge ((_ sign_extend 1) _let_27) _let_30))) (let ((_let_47 ((_ zero_extend 1) _let_25))) (let ((_let_48 ((_ sign_extend 2) _let_30))) (let ((_let_49 (bvslt _let_14 _let_22))) (let ((_let_50 (distinct ((_ sign_extend 3) _let_9) _let_12))) (let ((_let_51 (bvsge (bvadd _let_3 _let_2) v1))) (let ((_let_52 (bvule (ite (bvslt ((_ sign_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))) (bvadd (bvnot v0) (_ bv13 4))) (_ bv1 1) (_ bv0 1)) _let_19))) (let ((_let_53 (bvugt _let_34 v2))) (let ((_let_54 (bvugt _let_28 v1))) (let ((_let_55 (bvult (_ bv12 4) ((_ zero_extend 3) _let_4)))) (let ((_let_56 ((_ sign_extend 3) (ite (bvsle _let_28 _let_31) (_ bv1 1) (_ bv0 1))))) (let ((_let_57 (bvugt _let_24 _let_3))) (let ((_let_58 (bvugt (ite (= (bvnand (_ bv5 4) _let_2) _let_0) (_ bv1 1) (_ bv0 1)) (ite (bvsgt (_ bv13 4) (_ bv14 4)) (_ bv1 1) (_ bv0 1))))) (let ((_let_59 (bvslt _let_12 _let_56))) (let ((_let_60 ((_ zero_extend 3) (bvcomp (bvnot v0) (_ bv5 4))))) (let ((_let_61 ((_ zero_extend 3) _let_8))) (let ((_let_62 (bvslt v1 ((_ sign_extend 3) _let_26)))) (let ((_let_63 ((_ zero_extend 3) (bvnot (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))))) (let ((_let_64 (bvsle ((_ sign_extend 3) _let_11) (bvlshr (_ bv13 4) _let_7)))) (let ((_let_65 (bvule (bvxor v2 ((_ sign_extend 3) _let_4)) _let_63))) (let ((_let_66 (= ((_ zero_extend 3) _let_4) _let_22))) (let ((_let_67 (bvuge ((_ sign_extend 3) _let_16) _let_22))) (let ((_let_68 (bvult (ite (= (_ bv1 1) ((_ extract 0 0) (bvadd (bvnot v0) (_ bv13 4)))) ((_ zero_extend 3) _let_4) (bvlshr (_ bv13 4) _let_7)) (bvadd (bvnot v0) (_ bv13 4))))) (let ((_let_69 (= (_ bv6 4) _let_44))) (let ((_let_70 (bvsge (bvxnor ((_ sign_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4))) (bvand (_ bv6 4) (_ bv13 4))))) (let ((_let_71 (bvsge _let_16 _let_21))) (let ((_let_72 (bvuge ((_ sign_extend 3) _let_26) (bvadd (bvnot v0) (_ bv13 4))))) (let ((_let_73 ((_ sign_extend 3) _let_21))) (let ((_let_74 (bvugt (bvmul ((_ sign_extend 3) _let_4) (bvadd _let_3 _let_2)) v2))) (let ((_let_75 (bvsle _let_31 _let_14))) (let ((_let_76 (bvsge ((_ sign_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))) ((_ sign_extend 0) (_ bv5 4))))) (let ((_let_77 (bvsgt _let_35 _let_60))) (let ((_let_78 (bvsgt _let_17 ((_ sign_extend 3) _let_4)))) (let ((_let_79 (bvsge (bvand (_ bv6 4) (_ bv13 4)) _let_17))) (let ((_let_80 (bvsle (bvnand (_ bv5 4) _let_2) (bvnor (bvxnor (_ bv13 4) _let_7) (bvadd _let_12 _let_20))))) (let ((_let_81 (bvsle ((_ sign_extend 3) _let_36) _let_3))) (let ((_let_82 (bvuge ((_ sign_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))) (bvxnor (_ bv13 4) _let_7)))) (let ((_let_83 (bvule _let_45 (bvnor (bvxnor (_ bv13 4) _let_7) (bvadd _let_12 _let_20))))) (let ((_let_84 (distinct v2 (_ bv12 4)))) (let ((_let_85 (bvsge _let_9 _let_36))) (let ((_let_86 (bvult ((_ sign_extend 3) _let_26) v0))) (let ((_let_87 (bvslt ((_ zero_extend 0) _let_31) (bvor _let_15 (bvnot v0))))) (let ((_let_88 (bvuge _let_9 (ite (bvslt v0 (_ bv12 4)) (_ bv1 1) (_ bv0 1))))) (let ((_let_89 (bvugt _let_23 (ite (bvslt v0 (_ bv12 4)) (_ bv1 1) (_ bv0 1))))) (let ((_let_90 (bvugt _let_17 _let_32))) (let ((_let_91 (bvsge ((_ zero_extend 3) _let_4) (bvadd _let_3 _let_2)))) (let ((_let_92 (bvule (_ bv5 4) (bvnand (_ bv5 4) _let_2)))) (let ((_let_93 (bvuge _let_17 _let_29))) (let ((_let_94 (bvult _let_0 (bvadd _let_3 _let_2)))) (let ((_let_95 (bvsle (_ bv6 4) _let_18))) (let ((_let_96 (distinct ((_ sign_extend 3) (ite (bvule (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)) _let_26) (_ bv1 1) (_ bv0 1))) (bvnot v0)))) (let ((_let_97 (distinct ((_ sign_extend 3) (ite (bvsgt (bvmul ((_ zero_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) _let_1) _let_6) (_ bv1 1) (_ bv0 1))) _let_28))) (let ((_let_98 (bvsle _let_13 (bvadd _let_3 _let_2)))) (let ((_let_99 (bvslt v1 ((_ zero_extend 3) _let_4)))) (let ((_let_100 (distinct _let_24 _let_2))) (let ((_let_101 (not _let_62))) (let ((_let_102 (not _let_71))) (let ((_let_103 (not _let_72))) (let ((_let_104 (not _let_81))) (let ((_let_105 (not (bvugt _let_33 _let_33)))) (let ((_let_106 (not (bvslt (bvnot v0) ((_ sign_extend 3) _let_11))))) (let ((_let_107 (not (bvsle _let_45 v1)))) (let ((_let_108 (not (bvsge v3 _let_41)))) (let ((_let_109 (not _let_92))) (let ((_let_110 (not (bvsgt _let_60 _let_28)))) (let ((_let_111 (not (distinct _let_35 _let_20)))) (let ((_let_112 (not (bvsgt _let_35 ((_ rotate_left 1) (bvadd (bvnot v0) (_ bv13 4))))))) (let ((_let_113 (not (bvule _let_33 _let_16)))) (let ((_let_114 (not _let_57))) (let ((_let_115 (not (bvule ((_ zero_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4)))))) (let ((_let_116 (not (bvslt (_ bv6 4) _let_13)))) (let ((_let_117 (not _let_67))) (let ((_let_118 (not (distinct v1 (bvnand (_ bv5 4) _let_2))))) (let ((_let_119 (not (distinct (_ bv6 4) ((_ repeat 1) (_ bv14 4)))))) (let ((_let_120 (not _let_76))) (let ((_let_121 (not (distinct _let_6 ((_ sign_extend 1) _let_25))))) (let ((_let_122 (not (bvuge (bvnand (_ bv5 4) _let_2) _let_12)))) (let ((_let_123 (not _let_58))) (let ((_let_124 (not (= (bvmul ((_ sign_extend 3) _let_4) (bvadd _let_3 _let_2)) _let_12)))) (let ((_let_125 (not (bvuge ((_ sign_extend 3) _let_19) _let_29)))) (let ((_let_126 (not _let_85))) (let ((_let_127 (not _let_70))) (let ((_let_128 (not _let_100))) (let ((_let_129 (not (bvugt (bvnot v0) ((_ sign_extend 3) _let_4))))) (let ((_let_130 (not (bvsgt ((_ zero_extend 3) (bvnand (ite (bvsgt (_ bv13 4) ((_ sign_extend 3) (ite (bvslt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)) _let_11)) _let_24)))) (let ((_let_131 (not (bvuge _let_0 _let_45)))) (let ((_let_132 (not _let_97))) (let ((_let_133 (not (= _let_56 (bvxnor ((_ sign_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4))))))) (let ((_let_134 (not (bvsgt (_ bv6 4) (_ bv6 4))))) (let ((_let_135 (not _let_49))) (let ((_let_136 (not _let_91))) (let ((_let_137 (not (= (bvnand (_ bv5 4) _let_2) _let_13)))) (let ((_let_138 (not (bvsge ((_ sign_extend 3) _let_4) (_ bv14 4))))) (let ((_let_139 (not (bvsgt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1))))))) (let ((_let_140 (not (bvult (bvmul ((_ sign_extend 3) _let_4) (bvadd _let_3 _let_2)) _let_20)))) (let ((_let_141 (not (bvugt v0 ((_ sign_extend 3) _let_33))))) (and (or (not (bvsgt (bvxor v2 ((_ sign_extend 3) _let_4)) ((_ sign_extend 0) (_ bv5 4)))) _let_99 _let_94) (or _let_101 (not (bvule ((_ sign_extend 3) _let_33) v2)) _let_43) (or _let_102 _let_103 _let_104) (or (bvslt (_ bv6 4) _let_13) (not (= (bvlshr (_ bv13 4) _let_7) (bvnot v0))) (bvslt (bvxnor (_ bv13 4) _let_7) ((_ sign_extend 3) (ite (bvsgt (bvmul ((_ zero_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) _let_1) _let_6) (_ bv1 1) (_ bv0 1))))) (or _let_105 (bvslt _let_28 _let_35) _let_106) (or _let_107 (= _let_48 _let_29) _let_108) (or _let_109 (bvsgt _let_60 _let_28) (bvsgt ((_ zero_extend 3) (bvnand (ite (bvsgt (_ bv13 4) ((_ sign_extend 3) (ite (bvslt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)) _let_11)) _let_24)) (or (not _let_65) _let_110 (distinct _let_12 (bvadd (bvnot v0) (_ bv13 4)))) (or (not _let_93) _let_111 _let_53) (or (not _let_77) (bvsgt _let_35 ((_ rotate_left 1) (bvadd (bvnot v0) (_ bv13 4)))) _let_72) (or _let_68 (bvsgt ((_ zero_extend 3) _let_27) (bvor _let_15 (bvnot v0))) _let_112) (or (bvuge (_ bv14 4) (bvnor (_ bv5 4) (bvxnor ((_ sign_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4))))) _let_46 _let_53) (or (not _let_78) _let_84 _let_77) (or _let_113 (not _let_80) _let_114) (or (not _let_37) (not _let_96) _let_43) (or _let_50 (distinct _let_28 (bvxor v2 ((_ sign_extend 3) _let_4))) (bvuge ((_ sign_extend 3) _let_19) _let_29)) (or (bvsge ((_ zero_extend 3) _let_4) _let_18) (not _let_64) _let_115) (or (not _let_40) _let_116 _let_117) (or _let_118 (not _let_68) _let_50) (or (not (bvsge (ite (bvule (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)) _let_26) (_ bv1 1) (_ bv0 1)) (bvnot (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1))))) _let_62 _let_119) (or (not (bvugt _let_35 _let_47)) _let_89 _let_120) (or (not (bvule (ite (bvsgt (_ bv13 4) (_ bv14 4)) (_ bv1 1) (_ bv0 1)) (ite (bvslt ((_ sign_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))) (bvadd (bvnot v0) (_ bv13 4))) (_ bv1 1) (_ bv0 1)))) _let_121 (not _let_46)) (or _let_103 (= (bvxnor (_ bv13 4) _let_7) (bvnor (bvxnor (_ bv13 4) _let_7) (bvadd _let_12 _let_20))) _let_78) (or (not (= (bvlshr (_ bv13 4) _let_7) ((_ sign_extend 3) (ite (bvslt ((_ sign_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))) (bvadd (bvnot v0) (_ bv13 4))) (_ bv1 1) (_ bv0 1))))) (not (bvsle (bvxnor (_ bv13 4) _let_7) _let_61)) (bvugt v0 ((_ sign_extend 3) _let_33))) (or _let_92 _let_121 _let_122) (or _let_102 (not _let_94) _let_123) (or _let_82 (not _let_75) (not (distinct _let_35 ((_ sign_extend 3) _let_27)))) (or _let_58 (bvsle (bvadd _let_12 _let_20) _let_7) (not (bvsge (bvnor (_ bv5 4) (bvxnor ((_ sign_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4)))) _let_18))) (or (bvult ((_ repeat 1) (_ bv14 4)) ((_ sign_extend 3) (ite (bvsgt (_ bv13 4) ((_ sign_extend 3) (ite (bvslt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) _let_124 (not (bvsge _let_12 _let_35))) (or _let_125 _let_126 _let_57) (or _let_127 _let_120 _let_117) (or _let_127 _let_128 _let_123) (or _let_42 (bvsge ((_ sign_extend 3) _let_4) (_ bv14 4)) (bvule (bvor _let_15 (bvnot v0)) _let_29)) (or _let_98 (bvsgt _let_25 ((_ zero_extend 2) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1)))) _let_86) (or (distinct v0 _let_20) _let_104 (bvslt (_ bv6 4) (_ bv5 4))) (or (distinct v1 (bvnand (_ bv5 4) _let_2)) (distinct (bvnot v0) v2) _let_62) (or _let_70 _let_39 _let_129) (or (not _let_82) (distinct (ite (bvsgt (_ bv13 4) ((_ sign_extend 3) (ite (bvslt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)) _let_26) _let_93) (or (not _let_38) _let_96 _let_66) (or _let_80 (not (bvslt _let_2 _let_2)) (bvsgt (bvxnor ((_ sign_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4))) _let_7)) (or _let_130 _let_118 _let_109) (or _let_98 (not _let_52) (not (bvslt v0 (bvand (_ bv6 4) (_ bv13 4))))) (or _let_75 _let_131 _let_109) (or _let_100 (bvsle ((_ zero_extend 3) _let_33) _let_2) (not (bvuge _let_21 _let_36))) (or _let_94 (not _let_55) _let_37) (or (bvsge _let_5 (bvand (_ bv6 4) (_ bv13 4))) _let_132 (bvsle (_ bv13 4) ((_ sign_extend 3) (ite (= _let_10 (_ bv12 4)) (_ bv1 1) (_ bv0 1))))) (or _let_70 _let_133 _let_116) (or _let_86 _let_106 _let_134) (or _let_82 (bvsgt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))) _let_111) (or _let_118 _let_135 (bvuge (ite (bvsgt (_ bv13 4) ((_ sign_extend 3) (ite (bvslt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)) (ite (bvsgt (bvmul ((_ zero_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) _let_1) _let_6) (_ bv1 1) (_ bv0 1)))) (or (not _let_89) _let_71 _let_38) (or _let_136 _let_67 _let_136) (or _let_121 (bvsge v3 _let_45) _let_72) (or _let_76 _let_131 _let_71) (or _let_75 (bvsge ((_ sign_extend 3) _let_4) (_ bv14 4)) _let_137) (or _let_133 _let_42 (not _let_51)) (or (not (bvsge v2 (bvmul ((_ sign_extend 3) _let_4) (bvadd _let_3 _let_2)))) (not _let_86) _let_79) (or (not (bvsgt (bvmul ((_ zero_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) _let_1) (bvadd _let_3 _let_2))) _let_125 _let_112) (or _let_59 _let_40 _let_54) (or _let_88 (not (bvsge ((_ zero_extend 3) (ite (bvsle _let_28 _let_31) (_ bv1 1) (_ bv0 1))) (bvnor (_ bv5 4) (bvxnor ((_ sign_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4)))))) _let_115) (or _let_124 (not _let_88) _let_92) (or (bvugt _let_34 (bvadd (bvnot v0) (_ bv13 4))) _let_107 (not _let_74)) (or _let_95 _let_130 (not _let_99)) (or _let_49 (bvsgt (bvlshr (_ bv13 4) _let_7) _let_73) _let_90) (or _let_85 _let_67 (bvult _let_56 ((_ zero_extend 3) _let_4))) (or _let_43 _let_128 _let_138) (or _let_64 (not (bvult (bvcomp (bvnot v0) (_ bv5 4)) (ite (bvslt v0 (_ bv12 4)) (_ bv1 1) (_ bv0 1)))) _let_69) (or (bvule _let_28 ((_ zero_extend 3) (ite (= (bvnand (_ bv5 4) _let_2) _let_0) (_ bv1 1) (_ bv0 1)))) _let_139 _let_140) (or (bvuge _let_17 _let_44) (not _let_95) _let_108) (or _let_38 (bvult _let_28 _let_6) _let_105) (or (not (bvuge _let_41 _let_24)) _let_141 (bvult ((_ zero_extend 3) (ite (bvsgt (_ bv13 4) ((_ sign_extend 3) (ite (bvslt _let_0 ((_ sign_extend 3) (ite (= _let_1 _let_3) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1))) (bvnand (_ bv5 4) _let_2))) (or _let_104 _let_141 (not _let_87)) (or _let_65 _let_114 _let_74) (or _let_101 _let_110 _let_140) (or _let_135 _let_39 _let_116) (or _let_83 _let_129 _let_137) (or _let_91 _let_87 _let_139) (or _let_66 _let_79 _let_92) (or (bvugt _let_48 v3) (not (bvslt _let_61 _let_14)) (not (bvsgt ((_ zero_extend 3) _let_4) _let_14))) (or (bvuge ((_ zero_extend 0) _let_31) _let_63) _let_126 (= (bvmul ((_ zero_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) _let_1) v2)) (or (distinct _let_60 v1) _let_62 _let_122) (or (bvsge (bvnot v0) (bvxor v2 ((_ sign_extend 3) _let_4))) _let_76 (not _let_90)) (or _let_119 _let_138 _let_84) (or _let_46 _let_107 (bvsge (bvxnor ((_ sign_extend 3) (ite (bvugt _let_5 (bvnand (_ bv5 4) _let_2)) (_ bv1 1) (_ bv0 1))) (bvxor v2 ((_ sign_extend 3) _let_4))) _let_47)) (or (not _let_69) _let_55 (bvsgt (bvadd _let_3 _let_2) _let_14)) (or _let_97 _let_132 _let_52) (or (bvsgt _let_3 _let_35) _let_50 (bvsgt _let_73 ((_ repeat 1) (_ bv14 4)))) (or _let_54 _let_113 (not (distinct _let_0 v1))) (or _let_83 _let_51 _let_111) (or (not (= _let_12 _let_10)) _let_42 _let_59) (or _let_81 _let_134 _let_42)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) )
(check-sat)
