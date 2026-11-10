package LIAStarSolver
import ap.SimpleAPI
import ap.parser.{IConstant, IFormula, IFormulaITE, IExpression, ITermITE, IBoolLit, ITerm, IIntLit}
import ap.parser.IExpression.Int2ITerm
import LIAStarSolver.SatProcedure.SatProcedure
import LIAStarSolver.SatResult.{SatResult, Sat, Unsat}

@main def SumMain(): Unit = {

  val api: SimpleAPI = SimpleAPI.spawn
  //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
  val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
  val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

  //t*(t+1)/2 layers to sort for t minimal with 2^t >= N, here 3 plus start
  val maxLayers = 3  
  val layers = (0 to maxLayers).map(i => (0 to 3).map(j => api.createConstant(s"x$i$j")))

  //Connect Layers to unsorted and sorted variables
  val sortNetworkInit: Seq[IFormula] = {
    (0 to 3).map(i => (layers(0)(i) === X(i)) & (layers(maxLayers)(i) === Y(i)))
  }

  //Define compare and swap function
  def compSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
    val first = math.min(pos1, pos2)
    val second = math.max(pos1, pos2)
    ((layers(layer)(first) <= layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(first) & layers(layer + 1)(second) === layers(layer)(second)) | (layers(layer)(first) > layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(second) & layers(layer + 1)(second) === layers(layer)(first)))
  }

  //Propagate equality over layers
  def propLayer(ind: Seq[Int], layer: Int) =
    (for(x <- ind) yield layers(x)(layer + 1) === layers(x)(layer)).fold(IBoolLit(true))(_ & _)

  //sorting network (Batcher's merge-exchange) constraints (added algorithmically depending on N)
  val sortConstraints: Seq[IFormula] = Seq(
    //first layer
    compSwap(0,2,0),
    compSwap(1,3,0),
    propLayer(Seq.empty,0),
    //second layer
    compSwap(0,1,1),
    compSwap(2,3,1),
    propLayer(Seq.empty,1),
    //third layer
    compSwap(1,2,2),
    propLayer(Seq(0,3),2)
  )

  //Model sum(a0,v0,x0,x1), sum(a1,v1,x2,x3), a0[i]=5, a1=mapf(a0), x1=3, x2<0
  //First define f for convenience
  def f(in: ITerm, res: ITerm): IFormula = {
    ((2 === in) & (res === 2 * in)) | ((in =/= 2) & (res === 5 * in))
  }


  val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])
  val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
  val a0i = api.createConstant("a0[i]").asInstanceOf[IConstant]
  val a1i = api.createConstant("a1[i]").asInstanceOf[IConstant]
  val indi = api.createConstant("indi").asInstanceOf[IConstant]
  val v0 = api.createConstant("v0").asInstanceOf[IConstant]
  val v1 = api.createConstant("v1").asInstanceOf[IConstant]
  val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
  val Z = Z0.concat(Z1).concat(D)
  val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
  val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]
  println(Z)

  //sum constraints rewritten
  val sumConstraints: Seq[IFormula] = {
    val firstSum =
      (for(sumParts <- 0 to 2) yield
        ITermITE((X(0) <= Y(sumParts)) & (Y(sumParts + 1) <= X(1)), Z0(sumParts),0)).fold(IIntLit(0))(_ + _)
    val secondSum =
      (for(sumParts <- 0 to 2) yield
        ITermITE((X(2) <= Y(sumParts)) & (Y(sumParts + 1) <= X(3)), Z1(sumParts),0)).fold(IIntLit(0))(_ + _)
    val firstSummands = 
      (for(sumParts <- 0 to 2) yield
        ITermITE((X(0) <= Y(sumParts)) & (Y(sumParts + 1) <= X(1)), D(sumParts),0)).fold(IIntLit(0))(_ + _)
    val secondSummands = 
      (for(sumParts <- 0 to 2) yield
        ITermITE((X(2) <= Y(sumParts)) & (Y(sumParts + 1) <= X(3)), D(sumParts), 0)).fold(IIntLit(0))(_ + _)
    Seq(
      (v0 === firstSum + a0i), (v1 === secondSum + a1i), (summands0 === firstSummands), (summands1 === secondSummands))
    //Seq(v0 === firstSum, v1 === secondSum)
  }
  
  //Assume that x0 <= x1 and x2 <= x3
  //no other reads
  val constraints: Seq[IFormula] = Seq(
      (X(1) === 3),
      (X(2) < 0),
      (f(a0i,a1i)),
      v0 >= 6,
      a0i < 10,
      (v1 - v0) < 10,
      IFormulaITE((X(0) <= indi) & (indi <= X(1)), X(1) - X(0) === summands0, X(1) - X(0) === summands0 + 1),
      IFormulaITE((X(2) <= indi) & (indi <= X(3)), X(3) - X(2) === summands0, X(3) - X(2) === summands0 + 1)
      //X(1) - X(0) === summands0 + 1,
      //X(3) - X(2) === summands0 + 1
    )

  //Formula in star operator   
  val F: IFormula = {
    ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
    &
    ((0 to 2).map(i => ((D(i) === 0 & Z0(i) === 0 & Z1(i) === 0) | D(i) === 1)).reduce(_ & _))
    &
    (D(0) + D(1) + D(2) === 1)
  } 


  //Base formula
  val F0: IFormula = Seq(constraints, sortNetworkInit, sortConstraints, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)
  //println(F0)
  //println(F)
  val s = SatProcedure(api, F0, F, Z)
  val res: SatResult = s.checkFormulaWithTimingMeasurement(1)
  println(res)
  res match
    case Sat(m) => 
      api.!!(F0)
      for((x,y) <- m) api.!!(x === y)
      api.???
      println(api.partialModel)
      println(ap.util.Timer)
  api.shutDown

  // usage example 2:
  // expect unsat
  /*
  val api2: SimpleAPI = SimpleAPI.spawnWithAssertions
  val X2: Seq[IConstant] =
    api2.createConstants("x", 0 until 2) map (_.asInstanceOf[IConstant])
  val g2: IFormula = X2(0) === 4 & X2(1) === 7
  val f2: IFormula = X2(0) + X2(1) === 3

  val s2 = SatProcedure(api2, g2, f2, X2)
  val res2: SatResult = s2.checkFormula(1)
  println(res2)
  api2.shutDown
  */

}


@main def SumMain2(): Unit = {
  val api: SimpleAPI = SimpleAPI.spawn
    //sum(a1,v1,x0,x1) and sum(a2,v2,x2,x3)
    val X = (0 to 3).map(i => api.createConstant(s"x$i")) // N/2 sum constraints --> N values to sort in general, here 4
    val v0 = api.createConstant("v0").asInstanceOf[IConstant]
    val v1 = api.createConstant("v1").asInstanceOf[IConstant]


    //First define f for mapping constraint
    def f(in: ITerm, res: ITerm): IFormula = {
      (res === 5 * in)
    }

    
    
    //sorted sum bounds
    val Y = (0 to 3).map(i => api.createConstant(s"y$i"))

    //SORTING NETWORK
    //t*(t+1)/2 layers to sort for t minimal with 2^t >= N, here 3 plus start
    val maxLayers = 3  
    val layers = (0 to maxLayers).map(i => (0 to 3).map(j => api.createConstant(s"x$i$j")))

    //Connect Layers to unsorted and sorted variables
    val sortNetworkInit: Seq[IFormula] = {
      (0 to 3).map(i => (layers(0)(i) === X(i)) & (layers(maxLayers)(i) === Y(i)))
    }

    //Define compare and swap function
    def compSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
      val first = math.min(pos1, pos2)
      val second = math.max(pos1, pos2)
      ((layers(layer)(first) <= layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(first) & layers(layer + 1)(second) === layers(layer)(second)) | (layers(layer)(first) > layers(layer)(second) & layers(layer + 1)(first) === layers(layer)(second) & layers(layer + 1)(second) === layers(layer)(first)))
    }

    //Propagate equality over layers
    def propLayer(ind: Seq[Int], layer: Int) =
      (for(x <- ind) yield layers(layer + 1)(x) === layers(layer)(x)).fold(IBoolLit(true))(_ & _)

    //sorting network (Batcher's merge-exchange) constraints (can be added algorithmically depending on N, see Knuth 5.2.2)
    val sortConstraints: Seq[IFormula] = Seq(
      //first layer
      compSwap(0,2,0),
      compSwap(1,3,0),
      propLayer(Seq.empty,0),
      //second layer
      compSwap(0,1,1),
      compSwap(2,3,1),
      propLayer(Seq.empty,1),
      //third layer
      compSwap(1,2,2),
      propLayer(Seq(0,3),2)
    )

  

    //Translation to LIA*-constraints
    //Three copies for a0 and a1 for each segment
    val Z0 = (0 to 2).map(i => api.createConstant(s"z0$i").asInstanceOf[IConstant])    
    val Z1 = (0 to 2).map(i => api.createConstant(s"z1$i").asInstanceOf[IConstant])
    //Dummy variables to count summands and as flags
    val D = (0 to 2).map(i => api.createConstant(s"d$i").asInstanceOf[IConstant])
    //all variables in F
    val Z = Z0.concat(Z1).concat(D)
    //Sums and Summands counted in Star-Set
    val sum0 = api.createConstant("sum0").asInstanceOf[IConstant]
    val sum1 = api.createConstant("sum1").asInstanceOf[IConstant]
    val summands0 = api.createConstant("summands0").asInstanceOf[IConstant]
    val summands1 = api.createConstant("summands1").asInstanceOf[IConstant]


    //sum constraints rewritten
    val sumConstraints: Seq[IFormula] = {
      def calculateSums(low: ITerm, up: ITerm, z: Seq[IConstant]): (ITerm, ITerm) = {
        val selected = (0 to 2).map(i =>
          val cond = (low <= Y(i)) & (Y(i + 1) <= up)
          (ITermITE(cond, z(i), IIntLit(0)),ITermITE(cond, D(i), IIntLit(0))))
        selected.foldLeft((IIntLit(0): ITerm, IIntLit(0): ITerm))((x, y) => (x._1+y._1, x._2+y._2))
      }
      val first = calculateSums(X(0), X(1), Z0)
      val second = calculateSums(X(2), X(3), Z1)
      Seq(
        (sum0 === first._1), (sum1 === second._1), (summands0 === first._2), (summands1 === second._2))
    }
    
    //Constraints in F0
    val constraints: Seq[IFormula] = Seq(
        //Constraints for summation
        X(1) - X(0) === summands0,
        X(3) - X(2) === summands1,
        v0 === sum0,
        v1 === sum1,
        //LIA other constraints
        (X(1) === 3),
        (X(2) < 0),
        v0 === IIntLit(5)
        //v1 <= v0 + 40
      )

    //Formula in star operator   
    val F: IFormula = {
      ((0 to 2).map(i => ((D(i) === 1) ==> f(Z0(i),Z1(i)))).fold(IBoolLit(true))(_ & _))
      &
      ((0 to 2).map(i => (((D(i) === 0) ==> (Z0(i) === 0 & Z1(i) === 0)))).reduce(_ & _))
      &
      ((0 to 2).map(i => (D(i) >= 0)).fold(IBoolLit(true))(_ & _))
      &
      (D(0) + D(1) + D(2) === 1)
    } 

    //Base formula
    val F0: IFormula = Seq(constraints, sortNetworkInit, sortConstraints, sumConstraints).flatten.fold(IBoolLit(true))(_ & _)

    //Check Formula
    val procedure = SatProcedure(api, F0, F, Z)
    val obtained = procedure.checkFormulaWithTimingMeasurement(1)
    obtained match
      case Sat(m) => 
        api.!!(F0)
        for((x,y) <- m) api.!!(x === y)
        api.???
        println(api.partialModel)
        println(ap.util.Timer)
      case _ => 
        println("No Model found")
        println(ap.util.Timer)
    api.shutDown
}