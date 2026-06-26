import ap.SimpleAPI
import ap.parser._

import LIAStarSolver.SatProcedure.SatProcedure

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory

import LIAStarSolver.testhelpers.PrincessAssertions

class SatProcedureTests extends munit.FunSuite {

  test("_filterInductivePredicates(1): single predicate") {
    val api = SimpleAPI.spawnWithAssertions
    val X = Seq(api.createConstant("x").asInstanceOf[IConstant])
    val f = X(0) === 1
    val procedure = SatProcedure(api, true, f, X)

    val predicates = Seq(X(0) >= 0)
    val obtained = procedure._filterInductivePredicates(predicates)
    val expected = Seq(X(0) >= 0)
    assertEquals(obtained, expected)
  }

  test("_filterInductivePredicates(2)") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])

    val f = X(0) === 2 & X(1) > 0
    val procedure = SatProcedure(api, true, f, X)

    val predicates: Seq[IFormula] =
      Seq(X(0) >= 0, X(1) <= 10, (X(1) > -4 | X(0) === 3), X(1) > -2)
    val obtained = procedure._filterInductivePredicates(predicates)
    val expected = Seq(X(0) >= 0, (X(1) > -4 | X(0) === 3), X(1) > -2)
    assertEquals(obtained.toSet, expected.toSet)
    assertEquals(obtained.length, expected.length)
  }

  test("_filterInductivePredicates(mixed disjunction)") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])

    val f = X(0) === 2 & X(1) > 0
    val procedure = SatProcedure(api, true, f, X)

    val predicates: Seq[IFormula] =
      Seq(
        X(0) >= 0,
        X(1) > -2,
        (X(0) === 0 | X(1) > 0)
      )


    val obtained = procedure._filterInductivePredicates(predicates)
    val expected = Seq(
      X(0) >= 0,
      X(1) > -2,
    )

    assertEquals(obtained.toSet, expected.toSet)
    assertEquals(obtained.length, expected.length)
  }
}
