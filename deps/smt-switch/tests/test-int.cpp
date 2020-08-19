/*********************                                                        */
/*! \file test-int.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Tests for theory of integers.
**
**
**/

#include <utility>
#include <vector>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

class IntTests : public ::testing::Test,
                 public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    intsort = s->make_sort(INT);
  }
  SmtSolver s;
  Sort intsort;
};

TEST_P(IntTests, IntDiv)
{
  Term five = s->make_term(5, intsort);
  Term two = s->make_term(2, intsort);
  Term res = s->make_symbol("res", intsort);
  Term div = s->make_term(IntDiv, five, two);
  s->assert_formula(s->make_term(Equal, res, div));
  s->check_sat();
  Term resval = s->get_value(res);
  ASSERT_EQ(resval, two);
}

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverIntTests,
    IntTests,
    testing::ValuesIn(filter_solver_enums({ THEORY_INT })));

}  // namespace smt_tests
