#include <assert.h>
#include <fstream>

#include "opts.h"
#include "smt-switch/cvc4_factory.h"
#include "smt-switch/msat_factory.h"
#include "smtlibsolver.h"

using namespace lbv2i;
using namespace std;
using namespace smt;

int main(){
    //create SMT solver
    cout << "running OMT!\n";
    smt::SmtSolver s = smt::CVC4SolverFactory::create(false);
    //s->set_logic("QF_NIA");
    s->set_logic("ALL_SUPPORTED");
    s->set_opt("incremental", "true");
    s->set_opt("nl-ext-tplanes", "true");
    s->set_opt("produce-models", "true");
    s->set_opt("random-freq", "1");

    int bv_size = 8;        //The size in bits of our bitvector

    smt::Sort bvsort8 = s->make_sort(BV, bv_size);
    smt::Sort integer = s->make_sort(INT);
    smt::Sort boolean = s->make_sort(BOOL);

    smt::Term x = s->make_symbol("x", bvsort8);
    smt::Term y = s->make_symbol("y", bvsort8);

    smt::Term cost = s->make_symbol("cost", bvsort8);

    //make assertions for equations here
    smt::Term equation = s->make_term(Equal, s->make_term(BVSub, x, y), s->make_term(10, bvsort8));
    smt::Term cost_equation = s->make_term(Equal, s->make_term(BVAnd, x, y), cost);

    s->assert_formula(equation);
    s->assert_formula(cost_equation);

    s->push();

    int lb = 0;
    int ub = 255;       //should be bv max

    s->assert_formula(s->make_term(BVUle, s->make_term(lb, bvsort8), cost));      //pivot < area
    s->assert_formula(s->make_term(BVUge, s->make_term(ub, bvsort8), cost));         //area < ub

    smt::Result r = s->check_sat();

    if (!r.is_sat()){
        cout<<"there is no solution possible in the bounds given\n";
    }

    for (int i = bv_size-1; i >= 0; i--){
        int pivot = 1<<i;

        if (lb & pivot != 0){
            continue;
        }
        else{
            lb += pivot;
            s->pop();
            s->push();
            s->assert_formula(s->make_term(BVUle, s->make_term(lb, bvsort8), cost));
        }

        r = s->check_sat();

        if (r.is_sat()){
            cout<<"satisfied with lb = " << lb <<endl;
            smt::Term model_cost = s->get_value(cost);
            lb = model_cost->to_int();
            cout<<"model value is = " << model_cost << "converted: " << lb << endl;
        }
        else{
            cout<<"unsatisfied with lb = " << lb << endl;
            lb -= pivot;
        }
    }

    cout<< "max is : " << lb << endl;
}
