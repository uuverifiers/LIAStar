import LIAStarSolver.Linear.{vecLessThan, LinearSet}
import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.TestHelpers.TestHelpers

import ap.SimpleAPI
import ap.parser.IConstant

class UtilityTests extends munit.FunSuite with TestHelpers {
  test("vecLessThan") {
    assertEquals(vecLessThan(Vector(1, 2, 3), Vector(1, 9, 4)), true)
    assertEquals(vecLessThan(Vector(0, 0, 0), Vector(1, -90, 5)), true)
    assertEquals(vecLessThan(Vector(1, 2, -4), Vector(1, 2, -4)), true)
    assertEquals(vecLessThan(Vector(1, 2, 3), Vector(1, 1, -5)), false)
    assertEquals(vecLessThan(Vector(-0, 0, -1), Vector(0, 0, 4)), false)
  }
  test("LinearSet Equality test") {
    assertEquals(
      LinearSet(Vector(1, 2), Vector()),
      LinearSet(Vector(1, 2), Vector())
    )
    assertEquals(
      LinearSet(Vector(1, 2), Vector(Vector(4, 5), Vector(8, 9))),
      LinearSet(Vector(1, 2), Vector(Vector(8, 9), Vector(4, 5)))
    )
    assertEquals(
      LinearSet(
        Vector(1, 2),
        Vector(Vector(4, 5), Vector(8, 9), Vector(-4, 0))
      ),
      LinearSet(Vector(1, 2), Vector(Vector(-4, 0), Vector(8, 9), Vector(4, 5)))
    )
    assertEquals(
      LinearSet(Vector(1, 2), Vector(Vector(4, 5), Vector(8, 9))),
      LinearSet(
        Vector(1, 2),
        Vector(
          Vector(8, 9),
          Vector(4, 5),
          Vector(4, 5),
          Vector(4, 5),
          Vector(0, 0)
        )
      )
    )
    assertNotEquals(
      LinearSet(
        Vector(0, 2),
        Vector(Vector(4, 5), Vector(8, 9), Vector(-4, 0))
      ),
      LinearSet(Vector(1, 2), Vector(Vector(-4, 0), Vector(8, 9), Vector(4, 5)))
    )
  }

}
