import LIAStarSolver.Linear.{LinearSet, SemilinearSet}
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.TestHelpers.TestHelpers

import ap.SimpleAPI
import ap.parser.IConstant

class OffsetDownTests extends munit.FunSuite with TestHelpers {
  test("offsetDown: Empty B") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
    val f = (X(0) >= 0) & (X(1) <= 0)
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(4, 0),
      Vector()
    )

    val expected = None
    val obtained = ls.offsetDown(state)

    assertEquals(obtained, expected)
  }
  test("offsetDown: B only 0") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
    val f = (X(0) >= 0) & (X(1) <= 0)
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(4, 0),
      Vector(Vector(0, 0))
    )

    val expected = None
    val obtained = ls.offsetDown(state)

    assertEquals(obtained, expected)
  }
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

    val obtained = ls.offsetDown(state)
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
    assertEquals(obtained, expected)
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

    val obtained = ls.offsetDown(state)
    val obtainedReversed = ls.offsetDown(state)
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
    assertEquals(obtained, expected)
    assertEquals(obtainedReversed, expected)
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

    val obtained = ls.offsetDown(state)
    val expected = None
    assertEquals(obtained, expected)
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

    assertEquals(obtained, expected)
  }

  /////////////////////////////////////
  // SemilinearSet offset Down

  test("SLS offsetDown: Empty SLS") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val sls = SemilinearSet(Set())

    val obtained = sls.offsetDown(state)
    val expected = None
    assertEquals(obtained, expected)
  }

  test("SLS offsetDown: one LS with empty B") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(0), Vector())
    val sls = SemilinearSet(Set(ls1))

    val obtained = sls.offsetDown(state)
    val expected = None
    assertEquals(obtained, expected)
  }
  test("SLS offsetDown: one LS with 0 in B") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(0), Vector(Vector(0)))
    val sls = SemilinearSet(Set(ls1))

    val obtained = sls.offsetDown(state)
    val expected = None
    assertEquals(obtained, expected)
  }
  test("SLS offsetDown: single offsetDown-able ls") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(4), Vector(Vector(9), Vector(2)))
    val sls = SemilinearSet(Set(ls1))

    println(ls1.offsetDown(state))
    val obtained = sls.offsetDown(state)
    val expected = Some(
      SemilinearSet(Set(LinearSet(Vector(4), Vector(Vector(7), Vector(2)))))
    )
    assertEquals(obtained, expected)
  }
  test("SLS offsetDown: multiple ls, one offsetDown-able") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(4), Vector(Vector(-9), Vector(8)))
    val ls2 = LinearSet(Vector(4), Vector(Vector(9), Vector(2)))
    val ls3 = LinearSet(Vector(0), Vector(Vector(8), Vector(1)))
    val sls = SemilinearSet(Set(ls1, ls2, ls3))

    val obtained = sls.offsetDown(state)
    val expected = Some(
      SemilinearSet(
        Set(
          LinearSet(Vector(4), Vector(Vector(-9), Vector(8))),
          LinearSet(Vector(4), Vector(Vector(7), Vector(2))),
          LinearSet(Vector(0), Vector(Vector(8), Vector(1)))
        )
      )
    )
    assertEquals(obtained, expected)
  }

  test("SLS offsetDown: multiple offsetDown-able LS") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(4), Vector(Vector(3), Vector(8)))
    val ls2 = LinearSet(Vector(4), Vector(Vector(9), Vector(2)))
    val ls3 = LinearSet(Vector(0), Vector(Vector(8), Vector(1)))
    val sls = SemilinearSet(Set(ls1, ls2, ls3))

    val obtained = sls.offsetDown(state)
    val expected1 = Some(
      SemilinearSet(
        Set(
          LinearSet(Vector(4), Vector(Vector(5), Vector(3))),
          LinearSet(Vector(4), Vector(Vector(9), Vector(2))),
          LinearSet(Vector(0), Vector(Vector(8), Vector(1)))
        )
      )
    )
    val expected2 = Some(
      SemilinearSet(
        Set(
          LinearSet(Vector(4), Vector(Vector(3), Vector(8))),
          LinearSet(Vector(4), Vector(Vector(7), Vector(2))),
          LinearSet(Vector(0), Vector(Vector(8), Vector(1)))
        )
      )
    )
    assert(List(expected1, expected2).contains(obtained))
  }

}
