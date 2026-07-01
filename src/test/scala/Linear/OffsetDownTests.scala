
import LIAStarSolver.Linear.LinearSet
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.TestHelpers.TestHelpers

import ap.SimpleAPI
import ap.parser.IConstant

class OffsetDownTests extends munit.FunSuite with TestHelpers {
  test("offsetDown: simple replacement") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(0),
      Vector(
        Vector(5),
        Vector(2)
      )
    )

    val expected =
      Some(
        LinearSet(
          Vector(0),
          Vector(
            Vector(3),
            Vector(2)
          )
        )
      )

    val obtained = ls.offsetDown(state)

    assertEquivalentLSOptions(obtained, expected)
  }

  test("offsetDown: simple replacement 2d and reversed order") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(1, 2),
      Vector(
        Vector(2, 1),
        Vector(5, 4)
      )
    )
    val lsReversedB = LinearSet(
      Vector(1, 2),
      Vector(
        Vector(5, 4),
        Vector(2, 1)
      )
    )

    val expected =
      Some(
        LinearSet(
          Vector(1, 2),
          Vector(
            Vector(3, 3),
            Vector(2, 1)
          )
        )
      )

    val obtained = ls.offsetDown(state)
    val obtainedReversed = ls.offsetDown(state)

    assertEquivalentLSOptions(obtained, expected)
    assertEquivalentLSOptions(obtainedReversed, expected)
  }

  test("offsetDown: no b1 lessThan b2") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(1, 2),
      Vector(
        Vector(2, -1),
        Vector(5, 4),
        Vector(8, 1),
        Vector(1, -10)
      )
    )

    val expected = None

    val obtained = ls.offsetDown(state)

    assertEquivalentLSOptions(obtained, expected)
  }

  test("offsetDown: negative and equal coordinates") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
    val f = (X(0) >= 0) & (X(1) <= 0)
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(0, 0),
      Vector(
        Vector(2, -1),
        Vector(2, -5),
        Vector(1, -10)
      )
    )

    val expected = Some(
      LinearSet(
        Vector(0, 0),
        Vector(
          Vector(2, -1),
          Vector(0, -4),
          Vector(1, -10)
        )
      )
    )

    val obtained = ls.offsetDown(state)

    assertEquivalentLSOptions(obtained, expected)
  }

}
