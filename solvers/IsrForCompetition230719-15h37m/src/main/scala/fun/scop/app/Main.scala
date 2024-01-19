package fun.scop.app

object Main {
  def main(args: Array[String]) = {
    val inputs = readLine.split(' ').map(_.toInt)
    val area = inputs(0) * inputs(1)
    val periemeter = inputs(0) * 2 + inputs(1) * 2
    println(s"$area $periemeter")
  }
}
