package LIAStarSolver.SatResult

import ap.parser.IConstant
import ap.basetypes.IdealInt

sealed trait SatResult
type Model = Map[IConstant, IdealInt]
case object Unsat extends SatResult
case class Sat(model: Model) extends SatResult

