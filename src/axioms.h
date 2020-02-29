#pragma once

#include "smt-switch/smt.h"

namespace lbv2i {

class Axioms
{
 public:
  Axioms(smt::SmtSolver &solver);
  ~Axioms();

  // we assume that the term t looks like "fbvand(x, y)"
  // note the function name
  bool check_bvand_base_case(smt::Term t, smt::TermVec &outlemmas);
  bool check_bvand_max(smt::Term t, smt::TermVec &outlemmas);

 private:

  smt::Term pow2_minus_one(uint64_t k);

  smt::Term make_eq(smt::Term x, smt::Term y);
  smt::Term make_implies(smt::Term x, smt::Term y);

  void add_if_voilated(smt::Term l, smt::TermVec &out);

  smt::SmtSolver &solver_;

  smt::Sort int_sort_;

  smt::Term false_;

}; // class axioms

} // namespace lbv2i
