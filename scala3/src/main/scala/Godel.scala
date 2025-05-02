package godel

import scala.math.BigInt

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
  };

  def main(args: Array[String]): Unit = {
    primes.take(20).foreach(println)
  }
}
