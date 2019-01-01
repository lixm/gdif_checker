# gdif_checker

Type Checker for Globally Dependent Information Flow Policies

Ocaml versions 4.01.0 and 4.02.1 are tested under Mac OS X EL Capitan 

Ocaml version 4.01.0 is tested under Ubuntu 14.04

Ocaml version 4.02.1 is tested under Mac OS X High Sierra, and Mojave

Installation of the Z3 SMT solver with Ocaml bindings (https://github.com/Z3Prover/z3)
is required, Z3 version 4.4.2 is tested.

### Building the checker:

Bytecode:

ocamlc -custom -o gcifc.byte -I $Z3_HOME/build/api/ml/ -cclib "-L. -lz3" nums.cma z3ml.cma utils.ml lexer.ml ast.ml parser.ml ggraph.ml eqana.ml brana.ml lvana.ml z3utils.ml asst.ml valana.ml typing.ml gcifc.ml 

Native code:

ocamlopt -o gcifc -I $Z3_HOME/build/api/ml/ -cclib "-L. -lz3" nums.cmxa z3ml.cmxa utils.ml lexer.ml ast.ml parser.ml ggraph.ml eqana.ml brana.ml lvana.ml z3utils.ml asst.ml valana.ml typing.ml gcifc.ml 

In the above, $Z3_HOME/build/api/ml/ is the sub-directory for the z3 Ocaml API 
under the build directory of Z3

### Running the checker: 

Bytecode:

LD_LIBRARY_PATH=.  ./gcifc.byte <options> <file>

Native code

LD_LIBRARY_PATH=.  ./gcifc <options> <file>

In the above, <file> is an input file (currently the only example file is "fwfilter") and 
<options> is a non-empty list of switches explained in detail below. 

-rc Print the nodes and edges of the program graph in a form that can be vitualized using dot

-eq Print the result of the global analysis of available equalities

-br Print the results of the global analysis of branching decisions 

-lv Print the result of the live variables analysis

-asst Print the result of the local inference of pre/post-conditions

-val Print the information about the values of program variables, obtained by combining all the analyses on values and branching decisions

-plc Perform the type checking and display whether the policies are enforced 
