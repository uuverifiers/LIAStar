import LIAStarSolver.Linear.{LinearSet, SemilinearSet}
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.TestHelpers.TestHelpers

import ap.SimpleAPI
import ap.parser.IConstant

class ShiftDownTests extends munit.FunSuite with TestHelpers {
  test("shiftDown: empty B") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])

    val f = X(0) >= 0
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(5),
      Vector()
    )

    val expected = None
    val obtained = ls.shiftDown(state)

    assertEquals(obtained, expected)
  }
  test("shiftDown: B only 0") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])

    val f = X(0) >= 0
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(5),
      Vector(Vector(0))
    )

    val expected = None
    val obtained = ls.shiftDown(state)

    assertEquals(obtained, expected)
  }
  test("shiftDown:  Simple shift") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 1) map (_.asInstanceOf[IConstant])
    val f = X(0) >= 0
    val state = SolverState(api, true, f, X)
    val ls = LinearSet(Vector(5), Vector(Vector(2)))

    val expected: Option[LinearSet] =
      Some(LinearSet(Vector(3), Vector(Vector(2))))
    val obtained: Option[LinearSet] = ls.shiftDown(state)

    assertEquals(obtained, expected)
  }

  test("shiftDown: shift to zero") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])

    val f = X(0) >= 0
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(Vector(2), Vector(Vector(2)))

    val expected = Some(LinearSet(Vector(0), Vector(Vector(2))))
    val obtained = ls.shiftDown(state)

    assertEquals(obtained, expected)
  }

  test("shiftDown: no generator smaller than a") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])

    val f = true
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(Vector(2), Vector(Vector(5), Vector(-5)))

    val expected: Option[LinearSet] = None
    val obtained = ls.shiftDown(state)

    assertEquals(obtained, expected)
  }

  test("shiftDown: condition not valid") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])

    val f = X(0) >= 4
    // Not forall lambda>0; 5-2 + lambda*2 >= 4
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(Vector(5), Vector(Vector(2)))

    val expected: Option[LinearSet] = None
    val obtained = ls.shiftDown(state)

    assertEquals(obtained, expected)
  }
  test("shiftDown: multiple applicable generator") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])

    val f = X(0) >= 7
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(10),
      Vector(
        Vector(3),
        Vector(1),
        Vector(4)
      )
    )

    val expected1 =
      Some(
        LinearSet(
          Vector(9),
          Vector(
            Vector(1),
            Vector(3),
            Vector(4)
          )
        )
      )

    val expected2 =
      Some(
        LinearSet(
          Vector(7),
          Vector(
            Vector(4),
            Vector(3),
            Vector(1)
          )
        )
      )
    val obtained = ls.shiftDown(state)

    assert(List(expected1, expected2).contains(obtained))
  }

  test("shiftDown: two-dimensional shift") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])

    val f = (X(0) >= 0) & (X(1) >= 5)
    val state = SolverState(api, true, f, X)

    val ls = LinearSet(
      Vector(7, 50),
      Vector(
        Vector(2, 5)
      )
    )

    val expected =
      Some(
        LinearSet(
          Vector(5, 45),
          Vector(
            Vector(2, 5)
          )
        )
      )

    val obtained = ls.shiftDown(state)

    assertEquals(obtained, expected)
  }

  ////////////////////////////////
  // ShiftDown for SemilinearSet

  test("SLS shiftDown: empty SLS") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val sls = SemilinearSet(Set())

    val obtained = sls.shiftDown(state)
    val expected = None
    assertEquals(obtained, expected)
  }
  test("SLS shiftDown: one LS with empty B") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(0), Vector())

    val sls = SemilinearSet(Set(ls1))

    val obtained = sls.shiftDown(state)
    val expected = None
    assertEquals(obtained, expected)
  }
  test("SLS shiftDown: single shiftdownable ls") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(4), Vector(Vector(9), Vector(2)))
    val sls = SemilinearSet(Set(ls1))

    val obtained = sls.shiftDown(state)
    val expected = Some(
      SemilinearSet(Set(LinearSet(Vector(2), Vector(Vector(9), Vector(2)))))
    )
    assertEquals(obtained, expected)
  }
  test("SLS shiftDown: multiple ls, one shiftable") {
    val api = SimpleAPI.spawnWithAssertions
    val X = api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(4), Vector(Vector(-9), Vector(8)))
    val ls2 = LinearSet(Vector(4), Vector(Vector(9), Vector(2)))
    val ls3 = LinearSet(Vector(0), Vector(Vector(9), Vector(2)))
    val sls = SemilinearSet(Set(ls1, ls2, ls3))

    val obtained = sls.shiftDown(state)
    val expected = Some(
      SemilinearSet(
        Set(
          LinearSet(Vector(2), Vector(Vector(9), Vector(2))),
          LinearSet(Vector(4), Vector(Vector(-9), Vector(8))),
          LinearSet(Vector(0), Vector(Vector(9), Vector(2)))
        )
      )
    )
    assertEquals(obtained, expected)
  }
}
