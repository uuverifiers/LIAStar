# LIAStar-Solver

This repository contains an independent implementation of the LIA* solver proposed in *Solving LIA\* Using Approximations* by Levatich et al. 
It was developed as part of the bachelor's thesis *A Scala Implementation for Solving Linear Arithmetic with Stars*.

## Usage

Example usages can be found in `Main.scala`. The main entry point is

```scala
checkFormula(...)
```

The optional parameter `nUnfoldings` controls the number of unfoldings used by 
the overapproximation refinement procedure. 
Larger values may yield stronger interpolants but typically increase the cost of each refinement step.

For benchmarking, the method

```scala
checkFormulaWithTimingMeasurement(...)
```

returns the solver result whilst recording timing information for the individual phases of the algorithm.

## Main components

The implementation closely follows the algorithm presented in the paper. The central components are:

### `SatProcedure`

Coordinates the overall satisfiability procedure.

Responsibilities include:

* execution of the main refinement loop,
* checking the termination conditions,
* invoking the under- and overapproximation refinement procedures.

### `UnderapproximationRefiner`

Implements the refinement procedure of the underapproximation.
It constructs a semilinear set underapproximating `f`, applies the saturation rules, 
and computes the corresponding underapproximation of `f*` using the starLIA construction.

### `OverapproximationRefiner`

Implements the refinement procedure of the overapproximation.
It first checks whether the refinement preconditions are satisfied. If so, it obtains an interpolant
 from the SMT solver, maintains the conjunctions generated in previous refinement steps, 
 and computes the maximal inductive subset used as the updated overapproximation.

### `LinearSet`

Represents a linear set consisting of a shift vector and a set of offset vectors. Besides storing the representation,
 the class provides the saturation rules (Merge, ShiftDown, and OffsetDown) operations required during the underapproximation refinement.

### `SemilinearSet`

Represents a semilinear set as a collection of LinearSets. 
It provides operations for adding new linear sets and applying the saturation procedure.

### `SolverState`

Stores the current state of the algorithm, including

* the input formulae `g` and `f`,
* the current underapproximation,
* the current overapproximation,
* auxiliary data such as previously computed interpolants.

The state object is shared between the different algorithmic components.

### `FormulaFactory`

Provides helper methods for constructing and manipulating formulas.

Typical functionality includes

* substitution,
* construction of bounded unfoldings (`fLessN`),
* helper methods for constructing LIA formulas.

### `SMT`

Provides an abstraction over Princess.

It contains the SMT-related functionality required by the algorithm, including

* satisfiability checks,
* model generation,
* interpolation queries,

## Project Structure

```
SatProcedure/
    SatProcedure.scala
    UnderapproximationRefiner.scala
    OverapproximationRefiner.scala

SolverState/
    SolverState.scala

FormulaFactory/
    FormulaFactory.scala

Linear/
    LinearSet.scala
    SemilinearSet.scala
SMT/
    SMT.scala

SatResult.scala

Main.scala
```

## Note:
The timings presented in the bachelors thesis were created with 'TestTimingRunner.scala'
