from libcpp.string cimport string

cdef extern from "ops.h" namespace "smt":
    cdef cppclass c_SortKind "smt::SortKind":
        pass

    cdef cppclass c_PrimOp "smt::PrimOp":
        pass

    cdef cppclass c_ResultType "smt::ResultType":
        pass


cdef extern from "sort.h" namespace "smt":
    cdef c_SortKind c_ARRAY "smt::ARRAY"
    cdef c_SortKind c_BOOL "smt::BOOL"
    cdef c_SortKind c_BV "smt::BV"
    cdef c_SortKind c_INT "smt::INT"
    cdef c_SortKind c_REAL "smt::REAL"
    cdef c_SortKind c_FUNCTION "smt::FUNCTION"
    string to_string(c_SortKind sk) except +


cdef extern from "ops.h" namespace "smt":
    cdef c_PrimOp c_And "smt::And"
    cdef c_PrimOp c_Or "smt::Or"
    cdef c_PrimOp c_Xor "smt::Xor"
    cdef c_PrimOp c_Not "smt::Not"
    cdef c_PrimOp c_Implies "smt::Implies"
    cdef c_PrimOp c_Iff "smt::Iff"
    cdef c_PrimOp c_Ite "smt::Ite"
    cdef c_PrimOp c_Equal "smt::Equal"
    cdef c_PrimOp c_Distinct "smt::Distinct"
    # Uninterpreted Functions
    cdef c_PrimOp c_Apply "smt::Apply"
    # Arithmetic Theories
    cdef c_PrimOp c_Plus "smt::Plus"
    cdef c_PrimOp c_Minus "smt::Minus"
    cdef c_PrimOp c_Negate "smt::Negate"
    cdef c_PrimOp c_Mult "smt::Mult"
    cdef c_PrimOp c_Div "smt::Div"
    cdef c_PrimOp c_Lt "smt::Lt"
    cdef c_PrimOp c_Le "smt::Le"
    cdef c_PrimOp c_Gt "smt::Gt"
    cdef c_PrimOp c_Ge "smt::Ge"
    # Integers only
    cdef c_PrimOp c_Mod "smt::Mod"
    cdef c_PrimOp c_Abs "smt::Abs"
    cdef c_PrimOp c_Pow "smt::Pow"
    # Int/Real Conversion and Queries
    cdef c_PrimOp c_To_Real "smt::To_Real"
    cdef c_PrimOp c_To_Int "smt::To_Int"
    cdef c_PrimOp c_Is_Int "smt::Is_Int"
    # Fixed Size BitVector Theory
    cdef c_PrimOp c_Concat "smt::Concat"
    cdef c_PrimOp c_Extract "smt::Extract"
    cdef c_PrimOp c_BVNot "smt::BVNot"
    cdef c_PrimOp c_BVNeg "smt::BVNeg"
    cdef c_PrimOp c_BVAnd "smt::BVAnd"
    cdef c_PrimOp c_BVOr "smt::BVOr"
    cdef c_PrimOp c_BVXor "smt::BVXor"
    cdef c_PrimOp c_BVNand "smt::BVNand"
    cdef c_PrimOp c_BVNor "smt::BVNor"
    cdef c_PrimOp c_BVXnor "smt::BVXnor"
    cdef c_PrimOp c_BVComp "smt::BVComp"
    cdef c_PrimOp c_BVAdd "smt::BVAdd"
    cdef c_PrimOp c_BVSub "smt::BVSub"
    cdef c_PrimOp c_BVMul "smt::BVMul"
    cdef c_PrimOp c_BVUdiv "smt::BVUdiv"
    cdef c_PrimOp c_BVSdiv "smt::BVSdiv"
    cdef c_PrimOp c_BVUrem "smt::BVUrem"
    cdef c_PrimOp c_BVSrem "smt::BVSrem"
    cdef c_PrimOp c_BVSmod "smt::BVSmod"
    cdef c_PrimOp c_BVShl "smt::BVShl"
    cdef c_PrimOp c_BVAshr "smt::BVAshr"
    cdef c_PrimOp c_BVLshr "smt::BVLshr"
    cdef c_PrimOp c_BVUlt "smt::BVUlt"
    cdef c_PrimOp c_BVUle "smt::BVUle"
    cdef c_PrimOp c_BVUgt "smt::BVUgt"
    cdef c_PrimOp c_BVUge "smt::BVUge"
    cdef c_PrimOp c_BVSlt "smt::BVSlt"
    cdef c_PrimOp c_BVSle "smt::BVSle"
    cdef c_PrimOp c_BVSgt "smt::BVSgt"
    cdef c_PrimOp c_BVSge "smt::BVSge"
    cdef c_PrimOp c_Zero_Extend "smt::Zero_Extend"
    cdef c_PrimOp c_Sign_Extend "smt::Sign_Extend"
    cdef c_PrimOp c_Repeat "smt::Repeat"
    cdef c_PrimOp c_Rotate_Left "smt::Rotate_Left"
    cdef c_PrimOp c_Rotate_Right "smt::Rotate_Right"
    # BitVector Conversion
    cdef c_PrimOp c_BV_To_Nat "smt::BV_To_Nat"
    cdef c_PrimOp c_Int_To_BV "smt::Int_To_BV"
    # Array Theory
    cdef c_PrimOp c_Select "smt::Select"
    cdef c_PrimOp c_Store "smt::Store"
    string to_string(c_PrimOp op) except +


cdef extern from "ops.h" namespace "smt":
    cdef c_ResultType SAT
    cdef c_ResultType UNSAT
    cdef c_ResultType UNKNOWN


cdef class SortKind:
    cdef c_SortKind sk


cdef class PrimOp:
    cdef c_PrimOp po
