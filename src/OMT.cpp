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
    s->set_logic("QF_NIA");
    s->set_opt("incremental", "true");
    //s->set_opt("nl-ext-tplanes", "true");

    smt::Sort curr_sort = s->make_sort(INT);
    smt::Term perimeter = s->make_term(30, curr_sort);
    smt::Term x = s->make_symbol("x", curr_sort);
    smt::Term y = s->make_symbol("y", curr_sort);
    smt::Term addition = s->make_term(Plus, x, y);
    smt::Term formula = s->make_term(Equal, perimeter, addition);
    s->assert_formula(formula);

    int lb = 0;
    int ub = 300;

    smt::Term area = s->make_term(Mult, x, y);
    smt::Term area_formula_low = s->make_term(Le, s->make_term(lb, curr_sort), area);       //lb < area
    smt::Term area_formula_high = s->make_term(Ge, s->make_term(ub, curr_sort), area);       //area < ub

    s->push();
    s->assert_formula(area_formula_low);
    s->assert_formula(area_formula_high);

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
        s->assert_formula(s->make_term(Le, s->make_term(pivot, curr_sort), area));      //pivot < area
        s->assert_formula(s->make_term(Ge, s->make_term(ub, curr_sort), area));         //area < ub

        r = s->check_sat();

        if (r.is_sat()){
            lb = pivot;
        }
        else if (r.is_unsat()){
            ub = pivot;
        }
        else{
            cout <<"UNKNOWN\n";
            break;
        }
    }
    
    cout<<"the maximum value is " << lb <<"\n";
    cout<<"the maximum value is " << ub <<"\n";

    return 0;
}
