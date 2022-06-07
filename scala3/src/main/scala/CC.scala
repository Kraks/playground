package categorial.grammars

import scala.Conversion
import scala.language.postfixOps

case class NP[T](t: T) {
  def is(f: ADJ[T]): Boolean = f(t)
}
case class ADJ[T](f: T => Boolean) {
  def apply(t: T): Boolean = f(t)
}

given IntNPConv: Conversion[Int, NP[Int]] with
  def apply(n: Int): NP[Int] = NP(n)

given AdjConv[T]: Conversion[T => Boolean, ADJ[T]] with
  def apply(f: T => Boolean): ADJ[T] = ADJ(f)

//val even: Int => Boolean = n => n%2 == 0
def even(n: Int): Boolean = n % 2 == 0

object CCTest {
  def main(args: Array[String]): Unit = {
    val n: NP[Int] = 3
    val m: Boolean = 3 is even
    println(m)
    println(4 is even)
  }
}
