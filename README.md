# The SQLSI+ tool

This is an implementation for SQLSI+, as part of my Master thesis.
It is written in general-purpose programming language, namely Java and Python.

## Repository materials

The repository is structured as follows:

* `config`: stores the configuration (written in JSON) to run the Python script.
  * `Example1.json` corresponds to the Example 1 in the thesis.
  * `Example2.json` corresponds to the Example 2 in the thesis.
  * `Example3a.json` corresponds to the first half of Example 3 in the thesis.
  * `Example3b.json` corresponds to the second half of Example 3 in the thesis.
* `dm2msfol`: a Java module handling model-to-text transformation from Data model to MSFOL theory.
* `dmparser`: a Java module handling parsing Data model from JSON to Java objects.
* `ocl2msfol`: a Java module handling model-to-text transformation from OCL expressions to MSFOL theory.
* `oclparser`: a Java module handling parsing OCL expression from text to Java objects.
* `output`: stores the generated MSFOL theory.
  * `header.smt2` stores the default header of the generated file.
  * `theory.smt2` is the generated file.
* `result`: store the final result after solving the theory using SMT solver(s).
* `scripts`: store the Python script to generate and solve the theory.
* `smparser`: a Java module handling parsing Security model from JSON to Java objects.
* `solvers` stores SMT solvers
  * `CVC4`: the CVC4 solver.
  * `CVC4fmf`: the CVC4 solver, but using finite model finding capability.
  * `Z3` : the Z3 solver.
* `src` a Java integration of the above modules.

## Solution prerequisites

### Software Requirements
- (required) Python 3.1 (or higher), can be downloaded from https://www.python.org/downloads/.
- (required) Maven Apache and Java 1.8 (or higher).

* Note: Please note that, if you decided to use any other SMT solver of your choice, 
please create a corresponding folder with appropriate name in the parent folder *solvers*.
Put your solver inside this created folder and create an *solving.ini* file, indicate how
to run the solver.
