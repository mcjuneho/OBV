# Smt-Switch
A generic C++ API for SMT solving. It provides abstract classes which can be implemented by different SMT solvers.

# Architecture Overview

There are three abstract classes:
* `AbsSmtSolver`
* `AbsSort`
* `AbsTerm`

Each of them has a `using` statement that names a smart pointer of that type, e.g. `using Term = shared_ptr<AbsTerm>;`. The key thing to remember when using this library is that all solver-specific objects are pointers to the abstract base class. `SmtSolver`, `Sort`, and `Term` are all smart pointers. Note: there are many convenience functions which operate on these pointers, so they may not *look* like pointers. Additionally, the library also includes `using` statements for commonly used data structures, for example, `TermVec` is a vector of shared pointers to `AbsTerm`s.

The function names are based on SMT-LIB. The general rule is that functions/methods in this library can be obtained syntactically from SMT-LIB commands by replacing dashes with underscores. There are a few exceptions, for example `assert` is `assert_formula` in this library to avoid clashing with the `assert` macro. Operator names are also based on SMT-LIB operators, and can be obtained syntactically from an SMT-LIB operator by capitalizing the first letter and any letter after an underscore. The only exception is `bv` which is always capitalized to `BV` and does not count towards the capitalization of the first letter. Some examples include:

* `And`
* `BVAnd`
* `Zero_Extend`
* `BVAshr`

Please see the `tests` directory for some example usage.

# Creating a Smt-Switch Solver
To create a Smt-Switch solver through the API, first include the relevant factory header and then use the static `create` method. It takes a single boolean parameter which configures term logging. If passed `false`, the created `SmtSolver` relies on the underlying solver for term traversal and querying a term for the `Sort` or `Op`. If passed `true`, it instantiates a `LoggingSolver` wrapper which keeps track of the `Op`, `Sort` and children of terms as they are created. A `LoggingSolver` wraps all the terms and sorts created through the API. Thus, a `LoggingSolver` always returns a `LoggingTerm`. However, this is invisible to the user and all the objects can be used in the expected way. The logging feature is useful for solvers that alias sorts (for example don't distinguish between booleans and bitvectors of size one) or perform on-the-fly rewriting. The `LoggingSolver` wrapper ensures that the built term has the expected `Op`, `Sort` and children. In other words, the created term is exactly what was built through the API -- it cannot be rewritten or alias the sort. This drastically simplifies transferring between solvers and can be more intuitive than on-the-fly rewriting. Note: the rewriting still happens in the underlying solver, but this is hidden at the Smt-Switch level. Some solvers, such as `Yices2`, rely on the `LoggingSolver` for term traversal. E.g. creating a `Yices2` `SmtSolver` without term logging would not allow term traversal.

Here is an example that creates solver interface to CVC4:
```
#include "smt-switch/cvc4_factory.h"

int main()
{
  // create a CVC4Solver without logging
  smt::SmtSolver s = smt::CVC4SolverFactory::create(false);
  return 0;
}

```


# Operating Systems

Our `cmake` build system is currently only tested on Ubuntu Bionic and Mac OSX with XCode 9 but should work for other sufficiently modern (e.g. has C++17 support) Unix-based operating systems. Please file a GitHub issue if you have any problems!

# Solvers
To setup and install different solvers, first run the `./contrib/setup-<solver>.sh` script which builds position-independent static libraries in the `<solver>` directory. Then you can configure your `cmake` build with the `configure.sh` script. Enable a solver with `./configure.sh --<solver>`. By default only `libsmt-switch.so` is built without any solvers.

Some of the backend solvers have non-BSD compatible licenses. There are no provided setup scripts for these solvers. However, there are instructions for setting up these solvers in `./contrib`. Should you choose to link against these solver libraries, you assume all responsibility for meeting the license requirements of those libraries.

Once you've configured the build system, simply enter the build directory (`./build` by default) and run `make`. Each solver you add produces a `libsmt-switch-<solver>.so` shared object file. Running `make install` installs these libraries and the public header files into the configured prefix (`/usr/local` by default). Note that the header files are put in a directory, e.g. `/usr/local/include/smt-switch`.

## Currently Supported Solvers
* Boolector
* CVC4
* MathSAT
* Yices2

## Custom Solver Location
If you'd like to try your own version of a solver, you can use the `configure.sh` script to point to your custom location with `--<solver>-home`. You will need to build static libraries (.a) and have them be accessible in the standard location for that solver. For example, you would point to a custom location of CVC4 like so:
`./configure.sh --prefix=<your desired install location> --cvc4-home ./custom-cvc4`

where `./custom-cvc4/build/src/libcvc4.a` and `./custom-cvc4/build/src/parser/libcvc4parser.a` already exist. `build` is the default build directory for `CVC4`, and thus that's where `cmake` is configured to look.

# Building Tests
 You can build tests with `make test` from the build directory. After you have a full installation, you can build the tests yourself by updating the includes to include the `smt-switch` directory. For example: `#include "cvc4_factory.h"` -> `#include "smt-switch/cvc4_factory.h"`.

## Debug
The tests currently use C-style assertions which are compiled out in Release mode (the default). To build tests with assertions, please add the `--debug` flag when using `./configure.sh`.

# Python bindings
To compile python bindings, use the `--python` flag of `configure.sh`. By adding the flag `--py2`, you can ask CMake to use `python2`; however, this is not tested with CI. The python bindings require [Cython](https://cython.org). You can install Cython with `pip`. Note that by default, it uses `python3`, so be sure to install the `python3` version: `python3 -m pip install Cython`. If you're building the python bindings in a setting where you don't care too much about runtime speed (e.g. for CI), you can add the option `--install-option="--no-cython-compile"` to the end of the Cython installation command to install it faster. After configuring with python bindings, run `make` in the build directory as usual. The Python extension module will be `build/python/smt_switch.so`. To install this in your python environment, you can run `python3 -m pip install -e ./python` from the `build` directory.

## Testing python bindings
Python bindings are tested with [pytest](https://docs.pytest.org/en/latest/). This can be installed using `pip` and is automatically installed if you use the `setup.py` install from the `build` directory. To run all tests, simply run `pytest ./tests` from the top-level directory. Note, running `pytest` alone might unnecessarily run tests in dependencies located in subdirectories. To run a particular test, use the `-k test_name[parameter1-...-parameter_n]` format, e.g. `pytest -k test_bvadd[create_btor_solver]`.
