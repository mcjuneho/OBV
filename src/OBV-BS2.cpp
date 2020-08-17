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
    s->set_opt("bv-to-bool", "true");
    s->set_opt("bitwise-eq", "true");

    int bv_size = 8;        //The size in bits of our bitvector

    smt::Sort bvsort8 = s->make_sort(BV, bv_size);
    smt::Sort bvsort1 = s->make_sort(BV, 1);
    smt::Sort integer = s->make_sort(INT);
    smt::Sort boolean = s->make_sort(BOOL);

    smt::Term x = s->make_symbol("x", bvsort8);
    smt::Term y = s->make_symbol("y", bvsort8);

    smt::Term cost = s->make_symbol("c", bvsort8);

    //make assertions for equations here
    smt::Term equation = s->make_term(Equal, s->make_term(BVSub, x, y), s->make_term(10, bvsort8));
    smt::Term cost_equation = s->make_term(Equal, s->make_term(BVAnd, x, y), cost);

    s->assert_formula(equation);
    s->assert_formula(cost_equation);

    s->push();

    int lb = 0;
    int ub = 255;       //should be bv max

    int model_cost = 0;

    smt::Term one_bit = s->make_term(1, bvsort1);

    /*s->assert_formula(s->make_term(BVUle, s->make_term(lb, bvsort8), cost));      //pivot < area
    s->assert_formula(s->make_term(BVUge, s->make_term(ub, bvsort8), cost));         //area < ub
    */

    smt::Result r = s->check_sat();

    if (!r.is_sat()){
        cout<<"there is no solution possible in the bounds given\n";
    }

    smt::Term cost_model = s->get_value(cost);

    cout << one_bit << endl << "model cost is: " << cost_model->to_int() << endl;

    for (int i = bv_size-1; i >= 0; i--){

        smt::Op extract_bit = Op(Extract, i, i);
        smt::Term extracted_bit = s->make_term(extract_bit, cost);
        smt::Term extracted_bit_cost = s->make_term(extract_bit, cost_model);
        cout<< "extracted bit value: " << extracted_bit_cost << "\n";

        smt::Term assert_bit = s->make_term(Equal, extracted_bit, s->make_term(1, bvsort1));

        if (extracted_bit_cost == one_bit){
            cout<< "skipped a b-step"<<endl;
            //s->push();
            s->assert_formula(assert_bit);
            continue;
        }

        s->push();
        s->assert_formula(assert_bit);

        smt::Result r = s->check_sat();

        if (r.is_sat()){
            cout<< "equation sat with i: " << i << "\n";
            cost_model = s->get_value(cost);
            model_cost = s->get_value(cost)->to_int();
            cout<< "model cost is: " << model_cost << "\n";
        }
        else{
            cout << "equation unsat with i: " << i << "\n";
            s->pop();
        }
    }
}