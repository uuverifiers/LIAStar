import ap.SimpleAPI
import ap.parser._
import ap.basetypes.IdealInt

import LIAStarSolver.SatProcedure.SatProcedure

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SatResult._


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
    // all predicates are indidually inductive, but the combination not
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
      X(1) > -2
    )
    // remove the clause (X(0) === 0 | X(1) > 0) since e.g. for X=(0,-1)Y=(2,1)
    // !(predicates(X) & f(Y) => X(0)+Y(0) ==2 & X(1)+Y(1) > 0)

    assertEquals(obtained.toSet, expected.toSet)
    assert(
      obtained.length == expected.length && obtained.length == obtained.toSet.size
    )
  }

  test("___isOverapproximationTest") {
    // small test for the helper function ___isOverApproximationTest (which is only used for assertions)
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = X(0) === 2 & X(1) > 0
    val procedure = SatProcedure(api, true, f, X)

    assert(procedure.solverState.___isOverapproximationTest)
    procedure.solverState.overApproxFStar = X === 0 | X(0) > 0
    assert(procedure.solverState.___isOverapproximationTest)
    procedure.solverState.overApproxFStar = X === 0 | X(0) > 0 & X(1) > -1000
    assert(procedure.solverState.___isOverapproximationTest)

    procedure.solverState.overApproxFStar = X === 0 | X(0) > 0 & X(1) > 1
    assert(!(procedure.solverState.___isOverapproximationTest))
    procedure.solverState.overApproxFStar = (X(0) === 2)
    assert(!(procedure.solverState.___isOverapproximationTest))

  }

  ////////////////////////////////////////////////////
  // checkFormula Tests

  test("checkFormula: empty f, 0 in g") {
    val testname = "checkFormula: empty f, 0 in g"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g = X(0) === 0 & X(1) === 0
    val f = IExpression.i(false)
    val procedure = SatProcedure(api, g, f, X)
    val obtained = procedure.checkFormula()
    val expectedModelMap: Model = Map(X(0) -> 0, X(1) -> 0)
    obtained match {
      case Sat(Some(m)) => assertEquals(m, expectedModelMap)
      case Sat(None)    => true
      case Unsat        => fail("got Unsat, expected Sat")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
        true
      }
    }
  }

  test("checkFormula: empty f, 0 not in g") {
    val testname = "checkFormula: empty f, 0 not in g"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g = (X(1) + 2 * X(0) >= 17) &
      (6 * X(0) - X(1) <= 47)
    val f = false
    val procedure = SatProcedure(api, g, f, X)
    val obtained = procedure.checkFormula()
    obtained match {
      case Sat(_) =>
        fail(s"expected Unsat, got ${obtained}")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
        true
      }
      case Unsat => true
    }
  }
  test("checkFormula: empty g") {
    val testname = "checkFormula: empty g"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g = false
    val f = true
    val procedure = SatProcedure(api, g, f, X)
    val obtained = procedure.checkFormula()
    obtained match {
      case Sat(_) =>
        fail(s"expected Unsat, got ${obtained}")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
        true
      }
      case Unsat => true
    }
  }

  test("checkFormula: single solution") {
    val testname = "checkFormula: single solution"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g: IFormula = X(0) === 6 & X(1) === 3
    val f: IFormula = X(0) === 2 & X(1) === 1

    val procedure = SatProcedure(api, g, f, X)
    val obtained = procedure.checkFormula()
    val expectedModelMap: Model = Map(X(0) -> 6, X(1) -> 3)
    obtained match {
      case Sat(Some(m)) => assertEquals(m, expectedModelMap)
      case Sat(None) => println("INFO: Correct Sat result, but could not find model")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
        true
      }
      case Unsat =>
        fail(s"expected Sat, got ${obtained}}")
    }
  }

  test("checkFormula: single point g unsat") {
    val testname = "checkFormula: single point g unsat"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g: IFormula = X(0) === 5 & X(1) === 3
    val f: IFormula = X(0) === 2 & X(1) === 1
    val procedure = SatProcedure(api, g, f, X)

    val obtained = procedure.checkFormula()
    obtained match {
      case Sat(_)       => fail(s"expected Unsat, got ${obtained}")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
      }
      case Unsat => true
    }
    val expected = Unsat
    assertEquals(obtained, expected)
  }

  test("checkFormula: x plus y sat") {
    val testname = "checkFormula: x plus y sat"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g: IFormula = X(0) === 2 & X(1) === 7
    val f: IFormula = X(0) + X(1) === 3
    val procedure = SatProcedure(api, g, f, X)

    val obtained = procedure.checkFormula()
    println(s" x+y sat: ${obtained}")
    obtained match {
      // NOTE: this does not ensure this is actually a correct model
      case Sat(Some(m)) =>
        assert(m(X(0)) + m(X(1)) == IdealInt(9), "x+y!=9 in the returned Model")
      case Sat(None) => println("INFO: Correct Sat result, but could not find model")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
      }

      case Unsat => fail(s"expected Sat, got ${obtained}")
    }

  }

  test("checkFormula: x plus y unsat") {
    val testname = "checkFormula: x plus y unsat"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g: IFormula = X(0) === 4 & X(1) === 7
    val f: IFormula = X(0) + X(1) === 3
    val procedure = SatProcedure(api, g, f, X)

    val obtained = procedure.checkFormula()
    obtained match {
      case Sat(_)       => fail(s"expected Unsat, got ${obtained}")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
      }
      case Unsat => true
    }
  }

  test("checkFormula: g cone") {
    val testname = "checkFormula: g cone"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g: IFormula = (X(1) + 2 * X(0) >= 17) &
      (6 * X(0) - X(1) <= 47)
    val f: IFormula = (5 * X(0) + 2 * X(1) >= 17) &
      (3 * X(0) - X(1) <= 8) &
      (2 * X(0) + 3 * X(1) <= 20)
    val procedure = SatProcedure(api, g, f, X)

    val obtained = procedure.checkFormula()
    obtained match {
      case Sat(Some(m)) => {
        val x0 = m(X(0))
        val x1 = m(X(1))
        // NOTE: this only shows the returned model is in g, not necesarrily in f*!
        assert(x0 + 2 * x1 >= 17 && 6 * x0 - x1 <= 47)
      }
      case Sat(None) => println("INFO: Correct Sat result, but could not find model")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
      }
      case Unsat => fail("Expected Sat, got ${obtained}")

    }
  }
  test("checkFormula: unsat test") {
    val testname = "checkFormula: unsat test"
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val g: IFormula = (X(0) > 10 & X(1) === 1) |
      (X(0) <= 2 & X(0) + X(1) <= 2 & !(X(0) === 0 & X(1) === 0))
    val f: IFormula = X(0) >= 1 & X(1) >= 2
    val procedure = SatProcedure(api, g, f, X)

    val obtained = procedure.checkFormula()
    obtained match {
      case Sat(_)       => fail(s"expected Unsat, got ${obtained}")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase true "${testname}""""
        )
      }
      case Unsat => true
    }
  }
}
