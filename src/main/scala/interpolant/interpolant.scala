package LIAStarSolver.interpolant

import ap.parser.{IFormula, IExpression}
//import ap.parser.*
import ap.SimpleAPI

// calculate an Itp between f1->f2
class Interpolant(val f1: IFormula, val f2: IFormula) {

  // TODO:is IdealInt cast needed?
  // overApproximation of f*. All already inductive clauses
  var overApproxList: List[IFormula] = List()

  def getOverApproxFml: IFormula = {
    this.overApproxList.fold(IExpression.i(true)) {
      (x: IFormula, y: IFormula) => x & y
    }
  }

  /*
   * calculate a overapproximation from the given under approximation u
   */
  def calculateNextOverApproximation(u: IFormula) = {
    // TODO: get next Interpolant
    val Itp: IFormula = 5 <= 5

    // check forall

  }

  // ap.SimpleAPI.withProver(prover =>
  // import prover._
//
  // !!(g & getOverApproxFml)
  //
  //// TODO: checkSat vs ??? vs getStatus
  // if (??? == SimpleAPI.ProverStatus.Unsat){
  // true
  // } else {
  // false
  // }
  // )
  // }

}
