import ap.SimpleAPI
import ap.parser._

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory

case class TestEnv(
    api: SimpleAPI,
    state: SolverState,
    factory: FormulaFactory
)

trait PrincessAssertions extends munit.FunSuite {

  def assertEquivalent(
      api: SimpleAPI,
      a: IFormula,
      b: IFormula
  ): Unit = {

    api.push()
    api.!!(!(a <=> b))
    assertEquals(
      api.???,
      SimpleAPI.ProverStatus.Unsat
    )

    api.pop()
  }
}

class fLessNTest extends munit.FunSuite with PrincessAssertions {

  test("single element onedimensional f") {
    val api = SimpleAPI.spawnWithAssertions
    import api._
    val x = createConstant("x").asInstanceOf[IConstant]

    val f = x === 1

    val state = SolverState(api, true, f, Seq(x))
    val formulaFactory = FormulaFactory(state)

    val Y = state.createConstants("y_", 1)

    // 0 unfoldings
    val obtained0 = formulaFactory.fLessN(0, Y)
    val expected0 = Y(0) === 0
    assertEquivalent(api, obtained0, expected0)

    // 1 unfoldings
    var obtained1 = formulaFactory.fLessN(1, Y)
    var expected1 = Y(0) === 0 | Y(0) === 1

    assertEquivalent(api, obtained1, expected1)

    // 2 unfoldings
    val expected2 = Y(0) === 0 | Y(0) === 1 | Y(0) === 2
    val obtained2 = formulaFactory.fLessN(2, Y)
    assertEquivalent(api, obtained2, expected2)

    // 12 unfoldings
    val obtained3 = formulaFactory.fLessN(12, Y)
    val expected3 =
      Y(0) === 0 | Y(0) === 1 | Y(0) === 2 | Y(0) === 3 | Y(0) === 4 | Y(
        0
      ) === 5 | Y(0) === 6 | Y(0) === 7 | Y(0) === 8 | Y(0) === 9 | Y(
        0
      ) === 10 | Y(0) === 11 | Y(0) === 12
    assertEquivalent(api, obtained3, expected3)

  }

  test("single element, multidimensional f") {
    val api = SimpleAPI.spawnWithAssertions
    import api._
    val X: Seq[IConstant] =
      createConstants("x", 0 until 3) map (_.asInstanceOf[IConstant])
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

  test("half-space, two unfoldings") {
    import ap.parser.IExpression.ex

    val api = SimpleAPI.spawnWithAssertions
    import api._

    val X: Seq[IConstant] =
      createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])

    val f = (X(0) + X(1) >= 1)

    val state = SolverState(api, true, f, X)
    val formulaFactory = FormulaFactory(state)

    val Y = state.createConstants("y_", X.length)

    val obtained2 = formulaFactory.fLessN(2, Y)

    val expected2 =
      (Y(0) === 0 & Y(1) === 0) |
        (Y(0) + Y(1) >= 1) |
        (state.exVector(2) { x =>
          state.exVector(2) { z =>
            (x(0) + x(1) >= 1) &
              (z(0) + z(1) >= 1) &
              (Y(0) === x(0) + z(0)-1) &
              (Y(1) === x(1) + z(1))
          }
        })
    assertEquivalent(api, obtained2, expected2)
  }

}
