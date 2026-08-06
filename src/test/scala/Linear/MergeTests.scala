import LIAStarSolver.Linear.{LinearSet, SemilinearSet}
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.TestHelpers.TestHelpers

import ap.SimpleAPI
import ap.parser.IConstant


class MergeTests extends munit.FunSuite with TestHelpers {
  ////////////////////////////////////
  // Merge between linear sets
  test("LS merge: not lessequal") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(5, -4), Vector(Vector(1, 2)))
    val ls2 = LinearSet(Vector(3, -9), Vector(Vector(2, 0)))

    val obtained = ls1.merge(ls2, state)
    val expected = None
    assertEquals(obtained, expected)
    assertEquals(obtained, ls2.merge(ls1, state))
  }

  test("LS merge: simple merge") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = X(0) >= -5
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(3, -40), Vector(Vector(1, 2)))
    val ls2 = LinearSet(Vector(3, -9), Vector(Vector(2, 0)))

    val obtained = ls1.merge(ls2, state)
    val expected = Some(
      LinearSet(
        Vector(3, -9),
        Vector(Vector(1, 2), Vector(2, 0), Vector(0, -31))
      )
    )
    assertEquals(obtained, expected)
  }

  test("LS merge: single Point ls") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = X(0) + X(1) === 0
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(10, -10), Vector(Vector(1, -1)))
    val ls2 = LinearSet(Vector(5, -5), Vector())

    val obtained = ls1.merge(ls2, state)
    val expected =
      Some(LinearSet(Vector(5, -5), Vector(Vector(1, -1), Vector(5, -5))))
    assertEquals(obtained, expected)
    assertEquals(
      obtained,
      ls2.merge(ls1, state)
    ) // check "direction" doesn't matter
  }
  test("LS merge: condition on f not met") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 1) map (_.asInstanceOf[IConstant])
    val f = (X(0) >= 5 | X(0) === 1)
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(1), Vector(Vector(4)))
    val ls2 = LinearSet(Vector(9), Vector(Vector(3)))

    val expected = None
    assertEquals(ls1.merge(ls2, state), expected)
    assertEquals(
      ls2.merge(ls1, state),
      expected
    ) // check "direction" doesn't matter
  }

  test("LS merge: identical ls") {
    val api = SimpleAPI.spawnWithAssertions
    val X =
      api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(2, 3), Vector(Vector(1, 0)))
    val ls2 = LinearSet(Vector(2, 3), Vector(Vector(1, 0)))

    val expected =
      Some(
        LinearSet(Vector(2, 3), Vector(Vector(1, 0)))
      ) // Vector(0,0) in B doesn't make a difference
    assertEquals(ls1.merge(ls2, state), expected)
  }
  test("LS merge: two empty B's") {
    val api = SimpleAPI.spawnWithAssertions
    val X =
      api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = X(0) >= 2
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(2), Vector())
    val ls2 = LinearSet(Vector(5), Vector())

    val expected =
      Some(LinearSet(Vector(2), Vector(Vector(3))))
    assertEquals(ls1.merge(ls2, state), expected)
    assertEquals(ls2.merge(ls1, state), expected)
  }
  test("LS merge: one empty B") {
    val api = SimpleAPI.spawnWithAssertions
    val X =
      api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = X(0) >= 2
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(2), Vector(Vector(9)))
    val ls2 = LinearSet(Vector(5), Vector())

    val expected =
      Some(LinearSet(Vector(2), Vector(Vector(3), Vector(9))))
    assertEquals(ls1.merge(ls2, state), expected)
    assertEquals(ls2.merge(ls1, state), expected)
  }
  test("LS merge: B only 0") {
    val api = SimpleAPI.spawnWithAssertions
    val X =
      api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = X(0) >= 2
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(2), Vector(Vector(9)))
    val ls2 = LinearSet(Vector(5), Vector(Vector(0)))

    val expected =
      Some(LinearSet(Vector(2), Vector(Vector(3), Vector(9))))
    assertEquals(ls1.merge(ls2, state), expected)
    assertEquals(ls2.merge(ls1, state), expected)
  }
  test("LS merge: preserves all generators") {
    val api = SimpleAPI.spawnWithAssertions
    val X =
      api.createConstants("x", 0 until 2).map(_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(
      Vector(2, 1),
      Vector(
        Vector(1, 0),
        Vector(0, 1)
      )
    )
    val ls2 = LinearSet(
      Vector(4, 3),
      Vector(
        Vector(2, 2),
        Vector(-1, 0)
      )
    )

    val expected = Some(
      LinearSet(
        Vector(2, 1),
        Vector(
          Vector(1, 0),
          Vector(0, 1),
          Vector(2, 2),
          Vector(-1, 0)
        )
      )
    )
    assertEquals(ls1.merge(ls2, state), expected)
  }

  ////////////////////////////////////
  // Merge on semilinear set
  test("SLS merge: one mergable set-pair") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 1) map (_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(1), Vector(Vector(4)))
    val ls2 = LinearSet(Vector(9), Vector(Vector(3)))
    val ls3 = LinearSet(Vector(-1), Vector(Vector(3)))
    val sls = SemilinearSet(Set(ls1, ls2, ls3))

    val obtained = sls.merge(state)
    val expected = Some(
      SemilinearSet(
        Set(
          LinearSet(Vector(-1), Vector(Vector(3))),
          LinearSet(Vector(1), Vector(Vector(4), Vector(3), Vector(8)))
        )
      )
    )
    assertEquals(obtained, expected)
  }
  test("SLS merge: no  mergable set-pair") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(10, 5), Vector(Vector(4, 2)))
    val ls2 = LinearSet(Vector(11, 3), Vector(Vector(3, 3)))
    val ls3 = LinearSet(Vector(-1, 9), Vector(Vector(4, 4)))
    val ls4 = LinearSet(Vector(0, -7), Vector(Vector(3, 2)))
    val sls = SemilinearSet(Set(ls1, ls2, ls3, ls4))

    val expected = None
    val obtained = sls.merge(state)
    assertEquals(obtained, expected)
  }

  test("SLS merge: empty SLS") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)
    val sls = SemilinearSet(Set())

    val obtained = sls.merge(state)
    val expected = None
    assertEquals(obtained, expected)
  }
  test("SLS merge: one LS") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(10, 5), Vector(Vector(4, 2)))
    val sls = SemilinearSet(Set(ls1))

    val expected = None
    val obtained = sls.merge(state)
    assertEquals(obtained, expected)
  }
  test("SLS merge: multiple mergeable pairs") {
    val api = SimpleAPI.spawnWithAssertions
    val X =
      api.createConstants("x", 0 until 1).map(_.asInstanceOf[IConstant])
    val f = X(0) >= 1
    val state = SolverState(api, true, f, X)

    val ls1 = LinearSet(Vector(1), Vector(Vector(1)))
    val ls2 = LinearSet(Vector(3), Vector(Vector(2)))
    val ls3 = LinearSet(Vector(5), Vector(Vector(3)))

    val sls = SemilinearSet(Set(ls1, ls2, ls3))

    val obtained = sls.merge(state)
    val expected1 = Some(
      SemilinearSet(
        Set(
          LinearSet(Vector(1), Vector(Vector(1))),
          LinearSet(Vector(3), Vector(Vector(2), Vector(3)))
        )
      )
    )
    val expected2 = Some(
      SemilinearSet(
        Set(
          LinearSet(Vector(3), Vector(Vector(2))),
          LinearSet(Vector(1), Vector(Vector(1), Vector(3), Vector(4)))
        )
      )
    )
    val expected3 = Some(
      SemilinearSet(
        Set(
          LinearSet(Vector(5), Vector(Vector(3))),
          LinearSet(Vector(1), Vector(Vector(1), Vector(2)))
        )
      )
    )
    assert(List(expected1, expected2, expected3).contains(obtained))
  }

}
