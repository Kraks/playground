package types.cps

object CPSExamples {
  def power(x: Int, n: Int): Int =
    if (n == 0) 1
    else x * power(x, n-1)

  def power_cps(x: Int, n: Int, k: Int => Int): Int =
    if (n == 0) k(1)
    else power_cps(x, n-1, v => k(x * v))

  def fib(n: Int): Int =
    if (n == 0) 0
    else if (n == 1) 1
    else fib(n-1) + fib(n-2)

  def fib_cps(n: Int, k: Int => Int): Int =
    if (n == 0) k(0)
    else if (n == 1) k(1)
    else fib_cps(n-1, v1 => fib_cps(n-2, v2 => k(v1 + v2)))

  def map(xs: List[Int], f: Int => Int): List[Int] =
    xs match {
      case Nil => Nil
      case x :: xs => f(x) :: map(xs, f)
    }

  def map_cps(xs: List[Int], f: Int => (Int => List[Int]) => List[Int], k: List[Int] => List[Int]): List[Int] =
    xs match {
      case Nil => k(Nil)
      case x :: xs => f(x)(v => map_cps(xs, f, vs => k(v :: vs)))
    }

  def quicksort(xs: List[Int]): List[Int] = 
    xs match {
      case Nil => Nil
      case x :: xs =>
        val smaller = quicksort(xs.filter(_ <= x))
        val bigger = quicksort(xs.filter(_ > x))
        smaller ++ List(x) ++ bigger
    }

  def quicksort_cps(xs: List[Int], k: List[Int] => List[Int]): List[Int] =
    xs match {
      case Nil => k(Nil)
      case x :: xs =>
        quicksort_cps(xs.filter(_ <= x), smaller =>
          quicksort_cps(xs.filter(_ > x), bigger =>
            k(smaller ++ List(x) ++ bigger)))
    }

  def main(args: Array[String]) = {
    println(power_cps(2, 4, x => x))
    println(power_cps(3, 3, x => x))

    println(fib(3)) //2
    println(fib(8)) //21
    println(fib(12)) //144

    println(fib_cps(3, x => x)) //2
    println(fib_cps(8, x => x)) //21
    println(fib_cps(12, x => x)) //144

    println(map(List(1,2,3), x => x + 1))
    println(map_cps(List(1,2,3), x => k => k(x + 1), xs => xs))

    println(quicksort(List(5, 2, 4, 1, 0, 10)))
    println(quicksort_cps(List(5, 2, 4, 1, 0, 10), xs => xs))
  }
}
