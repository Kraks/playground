package types

object Unsound {
  trait A { type L >: Any }
  def id1(a: A, x: Any): a.L = x
  val p: A { type L <: Nothing } = null
  def id2(x: Any): Nothing = id1(p, x)

  def main(args: Array[String]) {
    id2("Oh")
  }
}
