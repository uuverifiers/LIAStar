import ap.SimpleAPI
import ap.parser._
import ap.basetypes.IdealInt

import LIAStarSolver.SatProcedure.OverapproximationRefiner

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.SatResult._


class OverapproximationRefinerTests extends munit.FunSuite {
  test("_filterInductivePredicates(1): single predicate") {
    val api = SimpleAPI.spawnWithAssertions
    val X = Seq(api.createConstant("x").asInstanceOf[IConstant])
    val f = X(0) === 1
    val state = SolverState(api, true, f, X)
    val factory = FormulaFactory(state)
    val nUnfoldings = 1 // not used for _filterInductivePredicates
    val refiner = OverapproximationRefiner(state, factory, nUnfoldings)


    val predicates = Seq(X(0) >= 0)

    val obtained = refiner._filterInductivePredicates(predicates)
    val expected = Seq(X(0) >= 0)
    assertEquals(obtained, expected)
  }
  test("_filterInductivePredicates(2)") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = X(0) === 2 & X(1) > 0
    val state = SolverState(api, true, f, X)
    val factory = FormulaFactory(state)
    val nUnfoldings = 1 // not used for _filterInductivePredicates
    val refiner = OverapproximationRefiner(state, factory, nUnfoldings)

    val predicates: Seq[IFormula] =
      Seq(X(0) >= 0, X(1) <= 10, (X(1) > -4 | X(0) === 3), X(1) > -2)

    val obtained = refiner._filterInductivePredicates(predicates)
    val expected = Seq(X(0) >= 0, (X(1) > -4 | X(0) === 3), X(1) > -2)
    assertEquals(obtained.toSet, expected.toSet)
    assertEquals(obtained.length, expected.length)
  }

  test("_filterInductivePredicates(3)") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = X(0) === 2 & X(1) > 0
    val state = SolverState(api, true, f, X)
    val factory = FormulaFactory(state)
    val nUnfoldings = 1 // not used for _filterInductivePredicates
    val refiner = OverapproximationRefiner(state, factory, nUnfoldings)

    val predicates: Seq[IFormula] =
      Seq(
        X(0) >= 0,
        X(1) > -2,
        (X(0) === 0 | X(1) > 0)
      )

    val obtained = refiner._filterInductivePredicates(predicates)
    val expected = Seq(
      X(0) >= 0,
      X(1) > -2
    )
    // remove the clause (X(0) === 0 | X(1) > 0) since e.g. for X=(0,-1)Y=(2,1)
    // !(predicates(X) & f(Y) => X(0)+Y(0) ==2 & X(1)+Y(1) > 0)

    assertEquals(obtained.toSet, expected.toSet)
    assert(
      obtained.length == expected.length && obtained.length == obtained.toSet.size
    )
  }

  test("_filterInductivePredicates(4)") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = (X(0) === 1 & X(1) === 1) | (X(0) === 3 & X(1) === 0)
    val state = SolverState(api, true, f, X)
    val factory = FormulaFactory(state)
    val nUnfoldings = 1 // not used for _filterInductivePredicates
    val refiner = OverapproximationRefiner(state, factory, nUnfoldings)

    val predicates: Seq[IFormula] =
      Seq(
        2*X(0) + X(1) <= 6,
        X(0) >= 0,
        X(1)<= 10
      )

    val obtained = refiner._filterInductivePredicates(predicates)
    val expected = Seq(
      X(0) >= 0,
    )
    // remove the clause (X(0) === 0 | X(1) > 0) since e.g. for X=(0,-1)Y=(2,1)
    // !(predicates(X) & f(Y) => X(0)+Y(0) ==2 & X(1)+Y(1) > 0)

    assertEquals(obtained.toSet, expected.toSet)
    assert(
      obtained.length == expected.length && obtained.length == obtained.toSet.size
    )
  }
}

