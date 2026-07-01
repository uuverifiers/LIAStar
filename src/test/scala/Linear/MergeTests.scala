import LIAStarSolver.Linear.{LinearSet, SemilinearSet}
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.TestHelpers.TestHelpers

import ap.SimpleAPI
import ap.parser.IConstant

// TODO: im allgemeinen ne helper function, um zu checken, dass alle LS in f sind in den testcases?

class MergeTests extends munit.FunSuite with TestHelpers {
  ////////////////////////////////////
  // Merge between linear sets
  test("merge: not lessequal") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(5, -4), Vector(Vector(1, 2)))
    val ls2 = LinearSet(Vector(3, -9), Vector(Vector(2, 0)))

    val expected = None
    val obtained = ls1.merge(ls2, state)
    assertEquals(obtained, expected)
    assertEquals(obtained, ls2.merge(ls1, state))
  }

  test("merge: simple merge") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = X(0) >= -5
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(3, -40), Vector(Vector(1, 2)))
    val ls2 = LinearSet(Vector(3, -9), Vector(Vector(2, 0)))

    val expected = Some(LinearSet(Vector(3, -9), Vector(Vector(1,2), Vector(2,0), Vector(0,-31))))
    val obtained = ls1.merge(ls2, state)
    assertEquals(obtained, expected)
  }

  test("merge: single Point ls") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
    val f = X(0) + X(1) === 0
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(10, -10), Vector(Vector(1, -1)))
    val ls2 = LinearSet(Vector(5, -5), Vector())

    val expected = Some(LinearSet(Vector(5, -5), Vector(Vector(1, -1), Vector(5, -5))))
    val obtained = ls1.merge(ls2, state)
    assertEquals(obtained, expected)
    assertEquals(obtained, ls2.merge(ls1, state)) // check "direction" doesn't matter
  }
  test("merge: condition on f not met") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 1) map (_.asInstanceOf[IConstant])
    val f = (X(0) >= 5 | X(0)=== 1)
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(1), Vector(Vector(4)))
    val ls2 = LinearSet(Vector(9), Vector(Vector(3)))

    val expected = None
    val obtained = ls1.merge(ls2, state)
    assertEquals(obtained, expected)
    assertEquals(obtained, ls2.merge(ls1, state)) // check "direction" doesn't matter
  }

  ////////////////////////////////////
  // Merge on semilinear set
  // TODO:
  test("devTesting") {
    val api = SimpleAPI.spawnWithAssertions
    val X: Seq[IConstant] =
      api.createConstants("x", 0 until 1) map (_.asInstanceOf[IConstant])
    val f = true
    val state = SolverState(api, true, f, X)
    val ls1 = LinearSet(Vector(1), Vector(Vector(4)))
    val ls2 = LinearSet(Vector(9), Vector(Vector(3)))
    val ls3 = LinearSet(Vector(-1), Vector(Vector(3)))
    val sls = SemilinearSet(Set(ls1, ls2, ls3))

    println("START OF PLAYING AROUND WITH TESTINGJ")
    val res = sls.merge(state)
    println(s"final res ${res}")
  }
}
