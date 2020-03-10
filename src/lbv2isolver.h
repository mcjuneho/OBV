#pragma once

#include <iostream>

#include "bv2int.h"
#include "preprocessor.h"
#include "axioms.h"

#include "smt-switch/smt.h"
#include "smt-switch/result.h"

namespace lbv2i {

class LBV2ISolver : public smt::AbsSmtSolver
{
 public:
  LBV2ISolver(smt::SmtSolver & solver, bool lazy = false);
  ~LBV2ISolver();

  smt::Result solve();

  void push(uint64_t num=1);
  void pop(uint64_t num=1);
  void reset();
  void reset_assertions();
  void set_logic(const std::string logic_name) const;
  void set_opt(std::string op, std::string value);
  void assert_formula(const smt::Term & f) const;
  smt::Term get_value(smt::Term & t) const;
  smt::Result check_sat();
  smt::Result check_sat_assuming(const smt::TermVec & assumptions);

  smt::Sort make_sort(const smt::SortKind sk) const;
  smt::Sort make_sort(const std::string name, uint64_t arity) const;
  smt::Sort make_sort(const smt::SortKind sk, uint64_t size) const;
  smt::Sort make_sort(const smt::SortKind sk, const smt::Sort & sort1) const;
  smt::Sort make_sort(const smt::SortKind sk,
                      const smt::Sort & sort1,
                      const smt::Sort & sort2) const;
  smt::Sort make_sort(const smt::SortKind sk,
                      const smt::Sort & sort1,
                      const smt::Sort & sort2,
                      const smt::Sort & sort3) const;
  smt::Sort make_sort(const smt::SortKind sk, const smt::SortVec & sorts) const;

  smt::Term make_symbol(const std::string name, const smt::Sort & sort);
  smt::Term make_term(const smt::Op op, const smt::TermVec & terms) const;
  smt::Term make_term(const smt::Op op, const smt::Term & t) const;
  smt::Term make_term(const smt::Op op,
                      const smt::Term & t0,
                      const smt::Term & t1) const;
  smt::Term make_term(const smt::Op op,
                      const smt::Term & t0,
                      const smt::Term & t1,
                      const smt::Term & t2) const;
  smt::Term make_term(const std::string val,
                      const smt::Sort & sort,
                      uint64_t base = 10);

  smt::Term make_term(bool b) const;
  smt::Term make_term(int64_t i, const smt::Sort & sort) const;
  smt::Term make_term(const smt::Term & val, const smt::Sort & sort) const;
  smt::Term make_term(const std::string val,
                      const smt::Sort & sort,
                      uint64_t base = 10) const;
  void run(std::string filename);

 private:
  bool refine(smt::TermVec & outlemmas);
  bool refine_bvand(const smt::TermVec &fterms, smt::TermVec & outlemmas);
  bool refine_bvor(const smt::TermVec &fterms, smt::TermVec & outlemmas);
  bool refine_bvxor(const smt::TermVec &fterms, smt::TermVec & outlemmas);

  // BV2Int Translator
  BV2Int * bv2int_;

  // Preprocessor that will eliminate some bv operators. Note: keep in mind
  // while writing the preprocessor that we want to use it also in the
  // incremental setting (push/pop)
  Preprocessor * prepro_;

  // axioms for refinement
  Axioms axioms_;

  // smt-switch solver
  smt::SmtSolver & solver_;

  bool lazy_;
};

}  // namespace lbv2i
