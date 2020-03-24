#pragma once

#include <gmpxx.h>
#include "smt-switch/smt.h"


class utils{

public:
  utils(smt::SmtSolver& solver);
  ~utils() {};
  smt::Term pow2(uint64_t k);
  smt::Term gen_intdiv(const smt::Term &a, const smt::Term &b, smt::TermVec& side_effects);
  smt::Term gen_mod(const smt::Term &a, const smt::Term &b, smt::TermVec& side_effects);
  smt::Term gen_bw(const smt::Op op, const uint64_t bv_width, uint64_t block_size, const smt::Term &a, const smt::Term &b, smt::TermVec& side_effects);
  static std::string pow2_str(uint64_t k);
  smt::Term make_range_constraint(const smt::Term & var, uint64_t bv_width);


  smt::Term fbvand_;
  smt::Term fbvor_;
  smt::Term fbvxor_;
  smt::Term fbvlshift_;
  smt::Term fbvrshift_;

private:
  smt::Term gen_euclid(smt::Term m, smt::Term n);
  smt::Term gen_bitwise_int(smt::Op op, uint64_t k, const smt::Term & x, const smt::Term & y);
  smt::Term gen_block(smt::Op op,
                       const smt::Term& a,
                       const smt::Term& b,
                       uint64_t i,
                       uint64_t block_size,
                       smt::TermVec& side_effects);



  smt::SmtSolver & solver_;
  smt::Sort int_sort_;
  smt::Term fintdiv_;
  smt::Term fintmod_;
  smt::Term int_zero_;
  smt::Term int_one_;

};
