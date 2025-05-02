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
    if (xs.isEmpty) Nil
    else {
      val smaller = quicksort(xs.tail.filter(_ <= xs.head))
      val bigger = quicksort(xs.tail.filter(_ > xs.head))
      smaller ++ List(xs.head) ++ bigger
    }

  def quicksort_cps(xs: List[Int], k: List[Int] => List[Int]): List[Int] =
    if (xs.isEmpty) k(Nil)
    else quicksort_cps(xs.tail.filter(_ <= xs.head), smaller =>
           quicksort_cps(xs.tail.filter(_ > xs.head), bigger =>
             k(smaller ++ List(xs.head) ++ bigger)))

  abstract class Tree
  case class Leaf() extends Tree
  case class Node(l: Tree, v: Int, r: Tree) extends Tree

  def treeFold[T](t: Tree, e: T, f: (T, Int, T) => T): T= t match {
    case Leaf() => e
    case Node(l, v, r) => f(treeFold(l, e, f), v, treeFold(r, e, f))
  }

  def treeSize(t: Tree) = treeFold[Int](t, 0, { case (lv, v, rv) => 1 + lv + rv })
  def treeDepth(t: Tree) = treeFold[Int](t, 0, { case (lv, v, rv) => 1 + math.max(lv, rv) })
  def treeReflect(t: Tree) = treeFold[Tree](t, Leaf(), { case (lv, v, rv) => Node(rv, v, lv) })

  def treeFold_cps[T](t: Tree, e: T, f: (T, Int, T) => (T => T) => T, k: T => T): T = t match {
    case Leaf() => k(e)
    case Node(l, v, r) => 
      treeFold_cps[T](l, e, f, lv => 
        treeFold_cps[T](r, e, f, rv => 
          f(lv, v, rv)(k)))
  }

  def anotherTreeSize(t: Tree) = 
    treeFold_cps[Int](t, 0, { case (lv, v, rv) => k => k(1 + lv + rv) }, t => t)
  def anotherTreeDepth(t: Tree) =
    treeFold_cps[Int](t, 0, { case (lv, v, rv) => k => k(1 + math.max(lv, rv)) }, t => t)
  def anotherTreeReflect(t: Tree) =
    treeFold_cps[Tree](t, Leaf(), { case (lv, v, rv) => k => k(Node(rv, v, lv)) }, t => t)

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

    val t1 = Node(Node(Leaf(), 1, Leaf()),
                  2,
                  Leaf())
    val t2 = Node(Node(Leaf(), 1, Leaf()),
                  2,
                  Node(Leaf(), 3, Node(Leaf(), 3, Leaf())))

    println(treeDepth(t2))
    println(anotherTreeDepth(t2))

    println(treeSize(t2))
    println(anotherTreeSize(t2))
    
    println(treeReflect(t1))
    println(anotherTreeReflect(t1))

    println(treeReflect(t2))
    println(anotherTreeReflect(t2))
  }
}
