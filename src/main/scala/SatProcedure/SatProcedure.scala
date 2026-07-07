package LIAStarSolver.SatProcedure

import ap.SimpleAPI
import ap.SimpleAPI.{ProverStatus, pp}
import ap.parser._
import ap.terfor.ConstantTerm

import LIAStarSolver.SolverState.SolverState
import LIAStarSolver.FormulaFactory.FormulaFactory
import LIAStarSolver.SMT.SMT
import LIAStarSolver.SatResult.{SatResult, Sat, Unsat, Inconclusive, Model}
import LIAStarSolver.Linear.{LinearSet, SemilinearSet}

class SatProcedure(
    solverInstance: SimpleAPI,
    g: IFormula,
    f: IFormula,
    X: Seq[IConstant]
) {

  val solverState = SolverState(solverInstance, g, f, X)
  val formulaFactory = FormulaFactory(solverState)

  // calculate if formula g(X) & f*(X) is sat or unsat
  def checkFormula(): SatResult = {

    // check if an exit criteria can be applied right from the start
    if (isEarlyUnsat) {
      println(
        s"DEBUG: EXIT: initial early unsat with overapprox ${pp(solverState.overApproxFStar)}"
      )
      return Unsat
    }

    val (earlySat, modelOptionRes): (Boolean, Option[Model]) = isEarlySat
    if (earlySat) {
      println(
        s"DEBUG: EXIT:  (initial) early sat with underapprox ${pp(solverState.underApproxFStar)}"
      )
      return Sat(modelOptionRes)
    }

    // setup for while loop
    val nUnfoldings = 2
    val Y: Seq[IConstant] = solverState.createConstants("y_", X.length)
    val fLess2nUnfoldingsOfY = formulaFactory.fLessN(
      2 * nUnfoldings,
      Y
    )
    val subst: Map[ConstantTerm, ITerm] =
      X.zip(Y)
        .map { case (x, y) =>
          x.asInstanceOf[IConstant].c -> (x + y)
        }
        .toMap
    val g_of_XplusY = ConstantSubstVisitor(g, subst)

    var _loopCount = 0 // TODO: only for debuggin purposes?!
    // this loop must converge at some point (could take infeasibly long)
    while (true) {
      println(s"\n\nDEBUG: top of while loop (iteration ${_loopCount})\n")
      _loopCount += 1

      //////////////////////////////
      // check convergence of underapproximation to f*
      val convergenceRes = checkUnderApproxConvergence
      if (convergenceRes.isDefined) {
        println(
          s"DEBUG: EXIT: u (${pp(solverState.underApproxFStar)} converged to f*"
        )
        return convergenceRes.get
      }

      //////////////////////////////
      // strengthen the Overapproximation

      // check underApprox(X) & f_less_2n(Y) & g(X+Y) unsat
      val unsatCondForStrengthenOver: IFormula =
        solverState.underApproxFStar & fLess2nUnfoldingsOfY & g_of_XplusY

      if (SMT.isUnsat(unsatCondForStrengthenOver, solverState)) {
        println("DEBUG: strengthen over")
        strengthenOverApproximation(nUnfoldings)
        println(
          s"DEBUG: strengthened overapprox: ${pp(solverState.overApproxFStar)}"
        )
      } else {
        println("DEBUG: Condition for applying strengthen over NOT met")
      }

      //////////////////////////////
      // check if exit criteria can be applied with the updated overapproximation
      if (isEarlyUnsat) {
        println(
          s"DEBUG: early unsat with overapprox ${pp(solverState.overApproxFStar)}"
        )
        return Unsat
      }

      //////////////////////////////
      // weaken the underapproximation

      // TODO: rename? not testing convergence here, but it is the same formula constructed for convergence
      val convergenceCondition = solverState.f & !solverState.underApproxFStar
      println("DEBUG____: calling getStatus for weakenUnder")
      val (proverStatus, modelOption) = SMT.getProverStatusAndModel(
        convergenceCondition,
        solverState.X,
        solverState
      )
      // since convergence criteria was unsat, a solution exists for f&!underapprox
      // TODO: Is neither Sat nor Unsat possible???? What about timeout or similar??????
      assert(proverStatus == ProverStatus.Sat)
      if (modelOption.isEmpty) {
        // no model can be constructed for f&!underApproximationOfFStar => algorithm can't continue
        return Inconclusive 
      }
      else {
        val solution_fAndNotUnderapprox: Model = modelOption.get

        weakenUnderApproximation(solution_fAndNotUnderapprox)
        println(
          s"DEBUG: WEAKENED underapproximation:${pp(solverState.underApproxFStar)}"
        )
      }

      //////////////////////////////
      // check if exit criteria can be applied with the updated underapproximation
      val (earlySat, modelOptionRes): (Boolean, Option[Model]) = isEarlySat
      if (earlySat) {
        println(
          s"DEBUG: early sat with underapprox ${pp(solverState.underApproxFStar)}"
        )
        return Sat(modelOptionRes)
      }

      println("\nDEBUG: bottom of while loop \n\n")

    }
    assert(true == false) // Can never reach here
    return Unsat // TODO: unreachable, maybe refactor
  }

  // return true if g & Overapproximation is unsat. Then g & f* must be unsat
  def isEarlyUnsat: Boolean = {
    SMT.isUnsat(g & solverState.overApproxFStar, solverState)
  }

  // return a if g & Underapproximation is sat. Then g & f* must also be sat.
  // If Sat and a model can be produced, return it as Some(Model)
  def isEarlySat: (Boolean, Option[Model]) = {
    println("DEBUG____: calling getStatus for isEarlySat")
    val (
      proverStatus,
      modelOption
    ) = SMT.getProverStatusAndModel(
      g & solverState.underApproxFStar,
      solverState.X,
      solverState
    )
    proverStatus match {
      case ProverStatus.Sat => (true, modelOption)
      case _                => (false, None)
    }
  }

  // Check if underApproximation has converged to f*. If so, return the SatResult for g&f*
  def checkUnderApproxConvergence: Option[SatResult] = {
    val convergenceCondition = solverState.f & !solverState.underApproxFStar
    if (SMT.isUnsat(convergenceCondition, solverState)) {
      // now g&underapproximation is equivalent to g&f*
      println(s"DEBUG  u has converged to f*")
      println("DEBUG____: calling getStatus for ")
      val (
        proverStatus,
        modelOption
      ) =
        SMT.getProverStatusAndModel(
          g & solverState.underApproxFStar,
          solverState.X,
          solverState
        )
      val returnValue = proverStatus match {
        case ProverStatus.Sat =>
          Sat(
            modelOption
          ) 
        case ProverStatus.Unsat => Unsat
        case _                  =>
          throw new Exception(
            "ProverStatus neither Sat or Unsat for g&f*"
          ) // TODO: Is this really an Exception and even reachable?
      }
      Some(returnValue)
    } else {
      // underApproxFStar has not yet converged
      None
    }
  }

  def strengthenOverApproximation(
      nUnfoldings: Int
  ): Unit = {
    import formulaFactory._
    // TODO: QUESTION: is this a problem, if i do it multiple times (already in checkFormula)
    val Y = solverState.createConstants("y_", solverState.X.length)
    val Z = solverState.createConstants("z_", solverState.X.length)

    val f1 =
      substituteX(solverState.underApproxFStar, Y) & fLessN(
        nUnfoldings,
        Z
      ) & X === (Y +++ Z)
    val YPrime = solverState.createConstants("yPrime_", solverState.X.length)
    val ZPrime = solverState.createConstants("zPrime_", solverState.X.length)
    val f2 = !(X === (YPrime +++ ZPrime) & fLessN(
      nUnfoldings,
      YPrime
    ) & substituteX(solverState.g, ZPrime))

    if (SMT.isUnsat(f1 & f2.notSimplify, solverState)) {
      // f1 ==> f2 is valid
      // get Interpolant between f1 and f2

      val itp = SMT.getInterpolant(f1, f2.notSimplify, solverState)
      // TODO: /NOTE itp has as variables X (in general, where to mention this,
      // how to make clear which variables occur for good readability/code clarity)
      println(s"DEBUG: in strengthenOver: find Interpolant ${pp(itp)}")
      solverState.overApproxFStar = _getNextOverApprox(itp)
    } else {
      println(
        "DEBUG: in strengthenOver: DONT find Interpolant => overapproximation stays the same"
      )
    }

    // TODO: remove this sanity check at the end of implementation
    assert(solverState.___isOverapproximationTest)
  }

  // TODO: Maybe extract into it's own class??
  // update the the conjuncts from all previous interpolations.
  // return the overapproximation resulting from these conjuncts
  def _getNextOverApprox(newItp: IFormula): IFormula = {
    val conjuncts = FormulaFactory.conjuncts(newItp)
    // TODO: make sure allInterpolantsConjuncts don't contain duplicates!?
    solverState.allInterpolantConjuncts =
      solverState.allInterpolantConjuncts ++ conjuncts

    val inductiveConjuncts = _filterInductivePredicates(
      solverState.allInterpolantConjuncts
    )

    if (inductiveConjuncts.length == 0)
      IExpression.i(true)
    else
      inductiveConjuncts.reduce(_ & _)

  }

  def _filterInductivePredicates(predicates: Seq[IFormula]): Seq[IFormula] = {

    // inductive iff:
    // forall x,y; remainingPredicates(x) & f(y) -> remainingPredicates(x+y)
    def isInductiveClause(
        p: IFormula,
        remainingPredicatesOfX: IFormula,
        fOfY: IFormula,
        substXWithXPlusY: Map[ConstantTerm, ITerm]
    ): Boolean = {
      val pOfXPlusY =
        ConstantSubstVisitor(p, substXWithXPlusY)
      val inductivnessTest =
        remainingPredicatesOfX & fOfY & !pOfXPlusY

      SMT.isUnsat(inductivnessTest, solverState)
    }

    var previousRemainingPredicates: Seq[IFormula] = Seq()
    var remainingPredicates = predicates
    val Y = solverState.createConstants("y_", solverState.X.length)

    // remove non Inductive predicates until convergance
    while (remainingPredicates != previousRemainingPredicates) {
      if (remainingPredicates == Seq())
        // worst case, no clause was inductive
        return Seq()
      previousRemainingPredicates = remainingPredicates

      // compute shared formulas for every p
      val remainingPredicatesOfX = remainingPredicates.reduce(_ & _)
      val fOfY = formulaFactory.substituteX(solverState.f, Y)
      val subst = (solverState.X zip Y).map { case (x, y) =>
        x.c -> (x + y)
      }.toMap

      remainingPredicates = for {
        p <- remainingPredicates
        if (isInductiveClause(p, remainingPredicatesOfX, fOfY, subst))
      } yield p
    }
    return remainingPredicates
  }

  def weakenUnderApproximation(solutionToAdd: Model): Unit = {
    val v = solverState.X.map(solutionToAdd).toVector
    println(s"DEBUG: WEAKEN UNDER, adding solution ${v} to U") // TODO
    solverState.underApproxF_SLS = solverState.underApproxF_SLS.addLS(
      LinearSet(v, Vector())
    )

    println(
      s"DEBUG: before Augment application ${solverState.underApproxF_SLS}"
    )

    var changed = true
    while (changed) {
      changed = false

      var shiftDownChange = true
      while (shiftDownChange) {
        shiftDownChange = false
        val shiftDownSLSOption: Option[SemilinearSet] =
          solverState.underApproxF_SLS.shiftDown(solverState)
        if (shiftDownSLSOption.isDefined) {
          shiftDownChange = true
          changed = true
          solverState.underApproxF_SLS = shiftDownSLSOption.get
        }
      }

      var offsetDownChange = true
      while (offsetDownChange) {
        offsetDownChange = false
        val offsetDownSLSOption: Option[SemilinearSet] =
          solverState.underApproxF_SLS.offsetDown(solverState)
        if (offsetDownSLSOption.isDefined) {
          changed = true
          offsetDownChange = true
          solverState.underApproxF_SLS = offsetDownSLSOption.get
        }
      }
      var mergeChange = true
      while (mergeChange) {
        mergeChange = false
        val mergeSLSOption: Option[SemilinearSet] =
          solverState.underApproxF_SLS.merge(solverState)
        if (mergeSLSOption.isDefined) {
          changed = true
          mergeChange = true
          solverState.underApproxF_SLS = mergeSLSOption.get
        }
      }
    }

    println(
      s"DEBUGs: after Augment application ${solverState.underApproxF_SLS}. Transforming this to underapprox via starLIA"
    )
    // convert SLS underapproximating f to a formula underapproximating f*
    solverState.underApproxFStar =
      formulaFactory.starLIA(solverState.underApproxF_SLS)
  }
}
