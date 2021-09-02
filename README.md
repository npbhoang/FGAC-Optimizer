# The FGAC-Optimizer tool

This is an implementation for SQLSI+, as part of my Master thesis.

## Repository materials

The repository is structured as follows:

* `config`: the configuration (written in JSON) to run the Python script.
* `dm2msfol`: module handling model-to-text transformation from Data model to MSFOL theory.
* `dmparser`: module handling parsing Data model from JSON to Java objects.
* `ocl2msfol`: module handling model-to-text transformation from OCL expressions to MSFOL theory.
* `oclparser`: module handling parsing OCL expression from text to Java objects.
* `output`: the generated MSFOL theory folder.
  * `header.smt2` the default header of the generated file.
  * `theory.smt2` the generated file.
* `result`: the satisfiability result after solving the theory.
* `scripts`: the Python script to generate and solve the MSFOL theory.
* `smparser`: module handling parsing Security model from JSON to Java objects.
* `solvers` stores SMT solvers execution commands.
  * `CVC4`: the CVC4 solver.
  * `CVC4fmf`: the CVC4 solver, but using finite model finding mode.
  * `Z3` : the Z3 solver.
* `src` a Java integration of the above modules.

## Solution prerequisites

### Software Requirements
- (required) Python 3.3 (or higher), can be downloaded from https://www.python.org/downloads/.
- (required) Maven 3 and Java 1.8 (or higher).

*Note*: to use any SMT solver, 
please create a corresponding folder with appropriate name in the parent folder *solvers*.
Put your solver inside this created folder and create an *solving.ini* file, indicate how
to run the solver.

### How to use the tool

#### First step: Define your data model and security model in JSON format.
- The data model and security model in JSON representation follows the definition in the thesis.
- Please store the models in the predefined folder, namely /src/main/resources.
- For example, consult a sample data model [here](https://github.com/npbhoang/sqlsi-/blob/00a6616542cd3175a8280991d25dcb4ca963d478/src/main/resources/university.json) and a sample security model [here](https://github.com/npbhoang/sqlsi-/blob/00a6616542cd3175a8280991d25dcb4ca963d478/src/main/resources/secVGU%232.json)
*Note*: Please remember to choose an entity as userClass.

#### Second step: Define your configuration file.
- The configuration file is a JSON object contains the following fields:
  - DataModel: the filename of the data model in JSON, without the suffix.
  - SecurityModel: the filename of the security model in JSON, without the suffix.
  - Invariants: (optional) an array of OCL expressions, written as String.
  - Role: a role, as String.
  - Resource: a target resource to be act, either an attribute or an association.
  - Properties: (optional) an array of OCL expressions, written as String.
  - Solvers: an array of solvers, at the moment, we support CVC4 and Z3.
  - Timeout: (optional) a timeout value, as an integer.
- Please store the configuration in the `/config` folder.
- For example, consult a sample configuration [here](https://github.com/npbhoang/sqlsi-/blob/00a6616542cd3175a8280991d25dcb4ca963d478/config/config.json).

#### Third step: Change the script and run it.
- Go to `/script/run.py`, change the content of line 15 to
```
CONFIG_FILENAME = '<config-file>.json'
```
where <config-file> is the filename of the configuration you want to run.
- Run the script via command:
```
python run.py -bes
```
where -b is to build the Java project by Maven, -e is to execute the generation of MSFOL theory and -s is to solve the theory using solvers.
- The result is stored in the `/results` folder.
