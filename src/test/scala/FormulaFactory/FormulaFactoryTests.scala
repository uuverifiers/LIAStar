import ap.SimpleAPI
import ap.parser._

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.Linear.{SemilinearSet, LinearSet}
import LIAStarSolver.FormulaFactory.FormulaFactory

import LIAStarSolver.TestHelpers.TestHelpers

class FormulaFactoryTests extends munit.FunSuite with TestHelpers {

  test("fLessN: f equals false") {
    val api = SimpleAPI.spawnWithAssertions
    val x = api.createConstant("x").asInstanceOf[IConstant]

    val f = false

    val state = SolverState(api, true, f, Seq(x))
    val formulaFactory = FormulaFactory(state)
    val Y = state.createConstants("y_", 1)

    // 0 unfoldings
    val obtained0 = formulaFactory.fLessN(0, Y)
    val expected0 = Y(0) === 0
    assertEquivalent(api, obtained0, expected0)

    // 20 unfoldings
    val expected1 = Y(0) === 0
    val obtained1 = formulaFactory.fLessN(20, Y)
    assertEquivalent(api, obtained1, expected1)
  }
  test("fLessN: f equals true") {
    val api = SimpleAPI.spawnWithAssertions
    val x = api.createConstant("x").asInstanceOf[IConstant]

    val f = true

    val state = SolverState(api, true, f, Seq(x))
    val formulaFactory = FormulaFactory(state)
    val Y = state.createConstants("y_", 1)

    // 0 unfoldings
    val obtained0 = formulaFactory.fLessN(0, Y)
    val expected0 = Y(0) === 0
    assertEquivalent(api, obtained0, expected0)

    // 1 unfoldings
    val expected1 = true
    val obtained1 = formulaFactory.fLessN(1, Y)
    assertEquivalent(api, obtained1, expected1)
  }

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
    assertEquivalent(api, obtained0, expected0)

    // 1 unfoldings
    val obtained1 = formulaFactory.fLessN(1, Y)
    val expected1 = Y(0) === 0 | Y(0) === 1
    assertEquivalent(api, obtained1, expected1)

    // 2 unfoldings
    val expected2 = Y(0) === 0 | Y(0) === 1 | Y(0) === 2
    val obtained2 = formulaFactory.fLessN(2, Y)
    assertEquivalent(api, obtained2, expected2)

    // 12 unfoldings
    val obtained3 = formulaFactory.fLessN(12, Y)
    val expected3 = 0 <= Y(0) & Y(0) <= 12
    assertEquivalent(api, obtained3, expected3)
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

    // 1 unfolding
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
        ex { (x1, x2, z1, z2) =>
          (x1 + x2 >= 1) &
            (z1 + z2 >= 1) &
            (Y(0) === x1 + z1) &
            (Y(1) === x2 + z2)
        }
    assertEquivalent(api, obtained2, expected2)
  }

  ////////////////////////////////////////////////
  // subsituteX tests

  test("substituteX: formula equals false or true") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = false
    val g = true
    val state = SolverState(api, g, f, X)
    val formulaFactory = FormulaFactory(state)

    val Y = state.createConstants("y_", 2)

    val obtained1 = formulaFactory.substituteX(state.f, Y)
    val expected1: IFormula = false
    assertEquals(obtained1, expected1)

    val obtained2 = formulaFactory.substituteX(state.g, Y)
    val expected2: IFormula = true
    assertEquals(obtained2, expected2)
  }
  test("substituteX: single dimension Test") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 1) map (_.asInstanceOf[IConstant])
    val f = X(0) === 9
    val g = X(0) >= 8 | X(0) =/= -20
    val state = SolverState(api, g, f, X)
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

  ///////////////////////////////
  // starLIA
  test("starLIA: empty sls") {
    import SimpleAPI.pp
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 1) map (_.asInstanceOf[IConstant])
    val state = SolverState(api, true, true, X)
    val formulaFactory = FormulaFactory(state)

    val sls = SemilinearSet(Set())

    val obtained = formulaFactory.starLIA(sls)
    val expected = X === 0
    assertEquivalent(api, obtained, expected)
  }
  test("starLIA: base 0") {
    import SimpleAPI.pp
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 1) map (_.asInstanceOf[IConstant])
    val state = SolverState(api, true, true, X)
    val formulaFactory = FormulaFactory(state)

    val ls1 = LinearSet(Vector(0), Vector(Vector(4), Vector(5)))
    val sls = SemilinearSet(Set(ls1))

    val obtained = formulaFactory.starLIA(sls)
    val expected = IExpression.ex((mu, lambda0, lambda1) =>
      (X(0) === (mu * 0 + lambda0 * 4 + lambda1 * 5)) &
        (mu === 0 ==> (lambda0 === 0 & lambda1 === 0)) &
        (mu >= 0 & lambda0 >= 0 & lambda1 >= 0)
    )
    assertEquivalent(api, obtained, expected)
  }

  test("StarLIA: base not 0") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val state = SolverState(api, true, true, X)
    val formulaFactory = FormulaFactory(state)

    val ls = LinearSet(Vector(2), Vector(Vector(3)))
    val sls = SemilinearSet(Set(ls))

    val expected = IExpression.ex((mu, lambda) =>
      (X(0) === mu * 2 + lambda * 3) &
        (mu === 0 ==> (lambda === 0)) &
        (mu >= 0 & lambda >= 0)
    )

    assertEquivalent(api, formulaFactory.starLIA(sls), expected)
  }

  test("StarLIA - negative base") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val state = SolverState(api, true, true, X)
    val formulaFactory = FormulaFactory(state)

    val ls = LinearSet(Vector(-2), Vector(Vector(5)))
    val sls = SemilinearSet(Set(ls))

    val expected = IExpression.ex((mu, lambda) =>
      (X(0) === mu * (-2) + lambda * 5) &
        (mu === 0 ==> (lambda === 0)) &
        (mu >= 0 & lambda >= 0)
    )

    assertEquivalent(api, formulaFactory.starLIA(sls), expected)
  }
  test("StarLIA: multiple ls(1)") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val state = SolverState(api, true, true, X)
    val formulaFactory = FormulaFactory(state)

    val ls1 = LinearSet(Vector(2), Vector(Vector(3)))
    val ls2 = LinearSet(Vector(5), Vector(Vector(7)))
    val sls = SemilinearSet(Set(ls1, ls2))

    val obtained = formulaFactory.starLIA(sls)
    val expected = IExpression.ex((mu1, lambda1, mu2, lambda2) =>
      (X(0) ===
        mu1 * 2 + lambda1 * 3 +
        mu2 * 5 + lambda2 * 7) &
        (mu1 === 0 ==> (lambda1 === 0)) &
        (mu2 === 0 ==> (lambda2 === 0)) &
        (mu1 >= 0 & lambda1 >= 0 &
          mu2 >= 0 & lambda2 >= 0)
    )

    assertEquivalent(api, obtained, expected)
  }
  test("StarLIA: multiple ls(2)") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val state = SolverState(api, true, true, X)
    val formulaFactory = FormulaFactory(state)

    val ls1 = LinearSet(Vector(1), Vector(Vector(4), Vector(6)))
    val ls2 = LinearSet(Vector(3), Vector(Vector(5)))

    val sls = SemilinearSet(Set(ls1, ls2))

    val obtained = formulaFactory.starLIA(sls)
    val expected = IExpression.ex((mu1, l10, l11, mu2, l20) =>
      (X(0) ===
        mu1 * 1 +
        l10 * 4 +
        l11 * 6 +
        mu2 * 3 +
        l20 * 5) &
        (mu1 === 0 ==> (l10 === 0 & l11 === 0)) &
        (mu2 === 0 ==> (l20 === 0)) &
        (mu1 >= 0 & l10 >= 0 & l11 >= 0 &
          mu2 >= 0 & l20 >= 0)
    )
    assertEquivalent(api, obtained, expected)
  }

  test("StarLIA: multidimensional") {
    import SimpleAPI.pp
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
    val state = SolverState(api, true, true, X)
    val formulaFactory = FormulaFactory(state)

    val ls1 = LinearSet(Vector(1, 3), Vector(Vector(4, 4), Vector(6, 9)))
    val ls2 = LinearSet(Vector(-4, 3), Vector(Vector(-10, 5)))

    val sls = SemilinearSet(Set(ls1, ls2))

    // NOTE: this formula is too complicated for princess to assert equality, so check printed formula.
    // This is implementation dependent, the test would not pass for every correct starLIA implementation.
    val obtained = pp(formulaFactory.starLIA(sls))
    // note: the vi are arranged in the order: lambdas descending, mus descending.
    // e.g la21 la12 la11 mu1 mu0 is v0 v1 v2 v3 v4
    val expected =
      """\exists int v0, v1, v2, v3, v4; (x0 = 1*v4 + 4*v2 + 6*v1 + -4*v3 + -10*v0 & x1 = 3*v4 + 4*v2 + 9*v1 + 3*v3 + 5*v0 & (v4 != 0 | (v2 = 0 & v1 = 0)) & (v3 != 0 | v0 = 0) & v4 >= 0 & v3 >= 0 & v2 >= 0 & v1 >= 0 & v0 >= 0)"""
    assertEquals(obtained, expected)
  }
}
