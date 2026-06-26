import ap.SimpleAPI
import ap.parser._

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory

import LIAStarSolver.testhelpers.PrincessAssertions

class FormulaFactorTests extends munit.FunSuite with PrincessAssertions {

  test("fLessN: single element onedimensional f") {
    val api = SimpleAPI.spawnWithAssertions
    val x = api.createConstant("x").asInstanceOf[IConstant]

    val f = x === 1

    val state = SolverState(api, true, f, Seq(x))
    val formulaFactory = FormulaFactory(state)

    val Y = state.createConstants("y_", 1)

    // 0 unfoldings
    val obtained0 = formulaFactory.fLessN(0, Y)
    val expected0 = Y(0) === 0
    val notExpected0 = Y(0) === 0 | Y(0) === 1
    assertEquivalent(api, obtained0, expected0)

    // 1 unfoldings
    val obtained1 = formulaFactory.fLessN(1, Y)
    val expected1 = Y(0) === 0 | Y(0) === 1
    val notExpected1 = Y(0) === 0

    assertEquivalent(api, obtained1, expected1)
    assertNotEquivalent(api, obtained1, notExpected1)

    // 2 unfoldings
    val expected2 = Y(0) === 0 | Y(0) === 1 | Y(0) === 2
    val obtained2 = formulaFactory.fLessN(2, Y)
    assertEquivalent(api, obtained2, expected2)

    // 12 unfoldings
    val obtained3 = formulaFactory.fLessN(12, Y)
    val expected3 = 0 <= Y(0) & Y(0) <= 12
    val notExpected3 = Y(0) <= 12
    assertEquivalent(api, obtained3, expected3)
    assertNotEquivalent(api, obtained3, notExpected3)

  }

  test("fLessN: single element, multidimensional f") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 3) map (_.asInstanceOf[IConstant])
    val f = X(0) === 1 & X(1) === -1 & X(2) === 0

    val state = SolverState(api, true, f, X)
    val formulaFactory = FormulaFactory(state)

    val Y = state.createConstants("y_", X.length)

    // 0 unfoldings
    val obtained0 = formulaFactory.fLessN(0, Y)
    val expected0 = (Y(0) === 0 & Y(1) === 0 & Y(2) === 0)
    assertEquivalent(api, obtained0, expected0)

    val obtained1 = formulaFactory.fLessN(1, Y)
    val expected1 = (
      Y(0) === 0 & Y(1) === 0 & Y(2) === 0
    ) | (
      Y(0) === 1 & Y(1) === -1 & Y(2) === 0
    )
    assertEquivalent(api, obtained1, expected1)
  }

  test("fLessN: half-space, two unfoldings") {
    import ap.parser.IExpression.ex

    val api = SimpleAPI.spawnWithAssertions

    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])

    val f = (X(0) + X(1) >= 1)

    val state = SolverState(api, true, f, X)
    val formulaFactory = FormulaFactory(state)

    val Y = state.createConstants("y_", X.length)

    val obtained2 = formulaFactory.fLessN(2, Y)

    val expected2 =
      (Y(0) === 0 & Y(1) === 0) |
        (Y(0) + Y(1) >= 1) |
        ex{ (x1,x2,z1,z2)  =>
            (x1 + x2 >= 1) &
              (z1 + z2 >= 1) &
              (Y(0) === x1 + z1) &
              (Y(1) === x2 + z2)
          }
    //val expected2 =
      //(Y(0) === 0 & Y(1) === 0) |
        //(Y(0) + Y(1) >= 1) |
        //(state.exVector(2) { x =>
          //state.exVector(2) { z =>
            //(x(0) + x(1) >= 1) &
              //(z(0) + z(1) >= 1) &
              //(Y(0) === x(0) + z(0)) &
              //(Y(1) === x(1) + z(1))
          //}
        //})
    assertEquivalent(api, obtained2, expected2)
  }

  test("substituteX: single dimension Test") {
    val api = SimpleAPI.spawnWithAssertions
    val x = api.createConstant("x").asInstanceOf[IConstant]
    val f = x === 9
    val g = x >= 8 | x =/= -20
    val state = SolverState(api, g, f, Seq(x))
    val formulaFactory = FormulaFactory(state)

    val Y = state.createConstants("y_", 1)

    val obtained1 = formulaFactory.substituteX(state.f, Y)
    val expected1 = Y(0) === 9
    assertEquals(obtained1, expected1)

    val obtained2 = formulaFactory.substituteX(state.g, Y)
    val expected2 = Y(0) >= 8 | Y(0) =/= -20
    assertEquals(obtained2, expected2)
  }
  test("substituteX: multi dimension Test") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 4) map (_.asInstanceOf[IConstant])
    val f = X(0) === 2 & X(1) < 7 & X(3) >= X(2)
    val state = SolverState(api, true, f, X)
    val formulaFactory = FormulaFactory(state)
    val Y = state.createConstants("y_", 4)

    val obtained1 = formulaFactory.substituteX(state.f, Y)
    val expected1 = Y(0) === 2 & Y(1) < 7 & Y(3) >= Y(2)
    assertEquals(obtained1, expected1)

  }

  test("substituteX: multi dimension Test") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 4) map (_.asInstanceOf[IConstant])
    val f = X(0) === 2 & X(1) < 7 & X(3) >= X(2)
    val state = SolverState(api, true, f, X)
    val formulaFactory = FormulaFactory(state)
    val Y = state.createConstants("y_", 4)

    val obtained1 = formulaFactory.substituteX(state.f, Y)
    val expected1 = Y(0) === 2 & Y(1) < 7 & Y(3) >= Y(2)
    assertEquals(obtained1, expected1)
  }


}
