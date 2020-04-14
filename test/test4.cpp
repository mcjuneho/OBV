#include "lbv2isolver.h"
#include "assert.h"

#include "smt-switch/msat_factory.h"
#include "smt-switch/cvc4_factory.h"
#include "smt-switch/smt.h"
#include "smt-switch/result.h"

using namespace lbv2i;
using namespace smt;
using namespace std;

int main() {
  SmtSolver underlying_solver = smt::CVC4SolverFactory::create();
  utils u(underlying_solver);
  Sort int_sort = underlying_solver->make_sort(INT);
  Term int_x = underlying_solver->make_term(10, int_sort);
  Term bv_x = u.int_val_to_bv_val(int_x, 4);
  cout << "panda int_x = " << int_x << endl;
  cout << "panda bv_x = " << bv_x << endl;

  //LBV2ISolver s = LBV2ISolver(underlying_solver);
  //s.set_logic("QF_UFBVNIA");
  //Sort bvsort8 = s.make_sort(BV, 8);
  //Term zero = underlying_solver->make_term(0, bvsort8);

  //Term x = s.make_symbol("x", bvsort8);
  //Term y = s.make_symbol("y", bvsort8);
  //Term z = s.make_symbol("z", bvsort8);
  //Term x_and_y = s.make_term(BVAnd, x, y);
  //Term x_add_y = s.make_term(BVAdd, x, y);
  //Term a = s.make_term(Equal, x_and_y, x_add_y);
  //s.assert_formula(a);
  //Result r = s.solve();
  //assert(r.is_sat());
}
