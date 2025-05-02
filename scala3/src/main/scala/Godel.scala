package godel

import math.BigInt
import BigInt.int2bigInt

object Godel {
  val fibs: LazyList[BigInt] =
    BigInt(0) #:: BigInt(1) #:: fibs.zip(fibs.tail).map{ n => n._1 + n._2 }
  //fibs.take(5).foreach(println)

  val nums: LazyList[BigInt] =
    BigInt(0) #:: nums.map(_ + 1)
  //nums.take(5).foreach(println)

  val nums2 = nums.drop(2)
  //nums2.take(5).foreach(println)
  val nums3 = nums.drop(3)

  // If i is not a multipler of a smaller prime number, then i is prime.
  val primes: LazyList[BigInt] = BigInt(2) #:: nums3.filter { i =>
    primes.takeWhile(k => k * k <= i).forall(k => i % k > 0)
  }

  //def BigIntPower(x: BigInt, n

  extension (x: BigInt)
    def **(n: BigInt): BigInt =
      if (n == BigInt(0)) BigInt(1)
      else x * (x ** (n - BigInt(1)))

  trait Expr {
    def godel: BigInt
  }
  case class Var(x: Int) extends Expr {
    def godel = (2 ** 0) * (3 ** x)
  }
  case class App(e1: Expr, e2: Expr) extends Expr {
    def godel = (2 ** 1) * (3 ** e1.godel) * (5 ** e2.godel)
  }
  case class Lam(x: Int, e: Expr) extends Expr {
    def godel = (2 ** 2) * (3 ** x) * (5 ** e.godel)
  }

  def reify(e: BigInt): Expr =
    if ((e mod BigInt(2)) == BigInt(0)) Var((e % 2).toInt)
    else ???

  def main(args: Array[String]): Unit = {
    //primes.take(20).foreach(println)

    val e = App(Lam(0, Var(0)), Lam(1, Var(1)))
    println(e.godel)

    println(Lam(0, Var(0)).godel)

    println(reify(Var(0).godel))
    println(reify(Var(5).godel))

    println(3 ** 3)
  }
}
