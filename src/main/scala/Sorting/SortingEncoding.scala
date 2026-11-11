package LIAStarSolver.Sorting

import ap.SimpleAPI
import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.IExpression._

object SortingEncoding {
  //The Sorting Network is an implementation of Knuths "The Art of Computer Programming" Volume 3, Section 5.2.2, Algorithm M (Batcher's Merge Exchange Sort). For better readability, we stick to the same notation for variable names.
  def sortingNetwork(
      X: Seq[IConstant],
      Y: Seq[IConstant],
      api: SimpleAPI
  ): Seq[IFormula] = {
    require(X.nonEmpty, "At least one input value is required")
    require(Y.length == X.length, "Input and output sequences must have the same length")
    //Initialize N, t as in the book
    val N = X.length
    val t = if N == 1 then 0 else math.ceil(math.log(N) / math.log(2)).toInt
    val maxLayers = t * (t + 1) / 2
    //Intermediate variables that need not be touched outside the sorting algitithm. They are used to propagate the values through the sorting network (layer by layer).
    val layers = (0 to maxLayers).map { _ =>
      api.createConstants(N).map(_.asInstanceOf[IConstant])
    }
    //Initial conditions: The first layer is equal to the input values, the last layer is equal to the output values.
    val init = for (i <- 0 until N)
      yield (X(i) === layers(0)(i)) & (Y(i) === layers(maxLayers)(i))

    def compareAndSwap(pos1: Int, pos2: Int, layer: Int): IFormula = {
      val first = math.min(pos1, pos2)
      val second = math.max(pos1, pos2)
      ((layers(layer)(first) <= layers(layer)(second) &
        layers(layer + 1)(first) === layers(layer)(first) &
        layers(layer + 1)(second) === layers(layer)(second)) |
        (layers(layer)(first) > layers(layer)(second) &
          layers(layer + 1)(first) === layers(layer)(second) &
          layers(layer + 1)(second) === layers(layer)(first)))
    }

    def propagate(indices: Seq[Int], layer: Int): IFormula =
      indices
        .map(index => layers(layer + 1)(index) === layers(layer)(index))
        .fold(IBoolLit(true))(_ & _)

    //Initital p (step M1 respectively initial distance)
    val initialDistance = math.pow(2, t - 1).toInt

    //merge is step M3 and M4 of the algorithm. Each call of merge adds a layer to the sorting network. To be precise a merge (as merge of k-sorted lists) can consist of multiple layers, in particular of multiple calls of the present function below.
    def merge(
        p: Int,
        q: Int,
        r: Int,
        d: Int,
        currentLayer: Int
    ): Seq[IFormula] = {
      val body =
        if currentLayer < maxLayers then {
          val compareLow = (0 until N - d).filter(i => (i & p) == r)
          val comparedIndices = compareLow.flatMap(i => Seq(i, i + d)).toSet
          val propagatedIndices = (0 until N).filterNot(comparedIndices.contains)
          compareLow.map(i => compareAndSwap(i, i + d, currentLayer)) :+
            propagate(propagatedIndices, currentLayer)
        } else {
          Seq.empty[IFormula]
        }

      if q != p then
        body ++ merge(p, q / 2, p, q - p, currentLayer + 1)
      else if p / 2 == 0 then
        body
      else
        val nextP = p / 2
        body ++ merge(nextP, initialDistance, 0, nextP, currentLayer + 1)
    }

    init ++ merge(initialDistance, initialDistance, 0, initialDistance, 0)
  }

  def bijectionSorting(
      X: Seq[IConstant],
      Y: Seq[IConstant],
      api: SimpleAPI
  ): Seq[IFormula] = {
    require(X.nonEmpty, "At least one input value is required")
    require(Y.length == X.length, "Input and output sequences must have the same length")

    val N = X.length
    val positions = api.createConstants(N).map(_.asInstanceOf[IConstant])
    val positionBounds =
      positions.map(position => (0 <= position) & (position <= IdealInt(N - 1)))
    val distinctPositions =
      (0 until N).flatMap(i => (0 until i).map(j => positions(i) =/= positions(j)))
    val valueMapping = for {
      outputIndex <- 0 until N
      inputIndex <- 0 until N
    } yield (positions(outputIndex) === IdealInt(inputIndex)) ==>
      (Y(outputIndex) === X(inputIndex))
    val sorted = (0 until N - 1).map(i => Y(i) <= Y(i + 1))

    positionBounds ++ distinctPositions ++ valueMapping ++ sorted
  }
}
