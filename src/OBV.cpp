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

    smt::Sort bvsort32 = s->make_sort(BV, 8);
    smt::Sort integer = s->make_sort(INT);

    smt::Term x = s->make_symbol("x", bvsort32);
    smt::Term y = s->make_symbol("y", bvsort32);

    smt::Term cost = s->make_symbol("c", bvsort32);

    //make assertions for equations here
    smt::Term equation = s->make_term(Equal, s->make_term(BVSub, x, y), s->make_term(10, bvsort32));
    smt::Term cost_equation = s->make_term(Equal, s->make_term(BVAnd, x, y), cost);

    s->assert_formula(equation);
    s->assert_formula(cost_equation);

    s->push();

    int lb = 0;
    int ub = 255;       //should be bv max 

    s->assert_formula(s->make_term(BVUle, s->make_term(lb, bvsort32), cost));      //lb < cost
    s->assert_formula(s->make_term(BVUle, cost, s->make_term(ub, bvsort32)));         //cost < ub

    smt::Result r = s->check_sat();

    if (!r.is_sat()){
        cout<<"there is no solution possible in the bounds given\n";
    }

    int iterations = 0;

    while(lb < ub && iterations < 100){
        //cout<<"lower bound: " << lb << "upper bound: " << ub << "\n";
        iterations++;
        int pivot = (lb + ub) / 2;
        s->pop();
        s->push();

        s->assert_formula(s->make_term(BVUlt, s->make_term(pivot, bvsort32), cost));      //pivot < cost
        s->assert_formula(s->make_term(BVUle, cost, s->make_term(ub, bvsort32)));         //cost < ub

        r = s->check_sat();

        if (r.is_sat()){
            if (pivot == lb){
                lb = ub;
            }
            else{
                lb = pivot;
            }
            cout<<"equation is sat with lower bound: " << lb << "upper bound: " << ub << "\n";
        }
        else if (r.is_unsat()){
            ub = pivot;
            cout<<"equation is unsat with lower bound: " << lb << "upper bound: " << ub << "\n";
        }
        else{
            cout <<"UNKNOWN\n";
            break;
        }
    }

    cout<<"max is " << lb << "\n" << "iterations: " << iterations;
    

    return 0;
}