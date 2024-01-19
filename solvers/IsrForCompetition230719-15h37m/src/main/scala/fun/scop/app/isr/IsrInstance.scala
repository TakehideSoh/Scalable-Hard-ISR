package fun.scop.app.isr

import fun.scop.app.Graph

case class IsrInstance(graph: Graph, init: Seq[Int], goal: Seq[Int]) {
  def getStats() = {
    (
      graph.nodes.size,
      graph.arcs.size,
      init.size,
      "%.2f".format(init.size.toDouble / graph.nodes.size),
      goal.size,
      "%.2f".format(goal.size.toDouble / graph.nodes.size)
    )
  }
}

object IsrInstance {

  private[this] def instanceFromFile(
      instanceFile: String
  ): (Seq[Int], Seq[Int]) = {
    val src = scala.io.Source.fromFile(instanceFile)

    var initial = Seq.empty[Int]
    var target = Seq.empty[Int]

    for (line <- src.getLines) {
      if (line.startsWith("s"))
        initial = line.split("\\s+").tail.toSeq.map(_.toInt)
      if (line.startsWith("t"))
        target = line.split("\\s+").tail.toSeq.map(_.toInt)
    }

    (initial, target)
  }

  def fromFile(graphFile: String, instanceFile: String): IsrInstance = {

    val graph = Graph.fromFile(graphFile, true)

    val (init, target) = instanceFromFile(instanceFile)

    IsrInstance(graph, init, target)

  }

}
