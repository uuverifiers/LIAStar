package LIAStarSolver.SemilinearSet



class SemilinearSet() {
  var linearSets: Set[LinearSet] = Set()

  def addLS(ls: LinearSet) = {
    // TODO: require same length?
    linearSets = linearSets + ls
  }

  def saturate() = {
    val changed = true
    while(changed) {

    }
  }

}
