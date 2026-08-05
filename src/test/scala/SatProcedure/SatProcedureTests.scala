import ap.SimpleAPI
import ap.parser._
import ap.basetypes.IdealInt
import ap.util.Timer

import LIAStarSolver.SatProcedure.SatProcedure

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.SatResult._



class SatProcedureTests extends munit.FunSuite {

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
      case Sat(m) => assertEquals(m, expectedModelMap) // (only one model)
      case Unsat        => fail("got Unsat, expected Sat")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase "${testname}""""
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
          s"""INFO: Inconclusive result for testcase "${testname}""""
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
          s"""INFO: Inconclusive result for testcase "${testname}""""
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
      case Sat(m) => assertEquals(m, expectedModelMap) // (only one model)
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase "${testname}""""
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
          s"""INFO: Inconclusive result for testcase "${testname}""""
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
    obtained match {
      // NOTE: this does not ensure this is actually a correct model
      case Sat(m) =>
        assert(m(X(0)) + m(X(1)) == IdealInt(9), "x+y!=9 in the returned Model")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase "${testname}""""
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

    val obtained = procedure.checkFormula(1)
    obtained match {
      case Sat(_)       => fail(s"expected Unsat, got ${obtained}")
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase "${testname}""""
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
      case Sat(m) => {
        val x0 = m(X(0))
        val x1 = m(X(1))
        // NOTE: this only shows the returned model is in g, not necesarrily in f*!
        assert(x0 + 2 * x1 >= 17 && 6 * x0 - x1 <= 47)
      }
      case Inconclusive => {
        println(
          s"""INFO: Inconclusive result for testcase "${testname}""""
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
          s"""INFO: Inconclusive result for testcase "${testname}""""
        )
      }
      case Unsat => true
    }
  }

}
