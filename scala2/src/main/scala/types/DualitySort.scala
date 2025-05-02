package duality.of.sorts

// A Duality of Sorts
// Ralf Hinze, Jose Pedro Magalhaes, Nicolas Wu
// in The Beauty of Functional Code, LNCS 8106

// This paper: makes the duality between folds and unfolds explicit,
//             defines sorting algorithms as folds of unfolds,
//             and as unfolds of folds.

object Sec1 {
  // insert an element `x` into an already sorted list `xs`
  def insert(x: Int, xs: List[Int]): List[Int] = {
    val (ys, zs) = xs.partition(_ <= x)
    ys ++ List(x) ++ zs
  }
  // insertion sort is the fold over the list with `insert`
  def insertSort(xs: List[Int]): List[Int] = xs.foldRight(List[Int]())(insert)

  // Example
  val xs = List(1, 3, 2, 10, 4, 3, 5)
  println(insertSort(xs))

  // unfold is a recursion scheme dual to fold, used to produce data, instead of consuming data.
  // `f : B => Option[(A, B)]` defines how to produce a list from a seed `B`,
  //   None corresponds to the empty list, Some((a, b)) corresponds to a list with element `a`
  //   and a new seed `b`.
  def unfoldRight[A, B](f: B => Option[(A, B)], b: B): List[A] = ???

  // selection sort picks the smallest element of an input list, and adds this element
  // to the result list (at its head).
  def selectSort(xs: List[Int]): List[Int] = unfoldRight(select, xs)

  // `select` the smallest element from an unordered list `xs`,
  // removes from the original list.
  def select(xs: List[Int]): Option[(Int, List[Int])] =
    if (xs.isEmpty) None 
    else {
      val min = xs.min
      val ys = delete(xs, min)
      Some((min, ys))
    }
  def delete[T](xs: List[T], x: T): List[T] = {
    val (before, atAndAfter) = xs.span(_ != x)
    before ++ atAndAfter.drop(1)
  }

  def main(args: Array[String]): Unit = ()
}

/* Sec 2. Functors, Folds, and Unfolds */

object Sec2 {
  // two-level types (Sheard & Pasalic 2004)
  // Level 1: describe the shape of the data
  abstract class List[+S]
  case object Nil extends List[Nothing]
  case class Cons[S](hd: Int, tl: S) extends List[S]

  // A fixed-point combinator/case class to build recursion
  case class Fix[F[_]](out: F[Fix[F]])

  // Level 2: describe the recursion
  type Lst = Fix[List]

  // Examples
  val xs: Fix[List] = Fix[List](Nil)
  val ys: Fix[List] = Fix[List](Cons[Fix[List]](1, Fix[List](Nil)))
  val zs: Fix[List] = Fix[List](Cons(1, Fix[List](Cons(2, Fix[List](Cons(3, Fix[List](Nil)))))))
  val unsorted: Fix[List] = Fix[List](Cons(3, Fix[List](Cons(2, Fix[List](Cons(1, Fix[List](Nil)))))))

  // Functor definitions/operations
  trait Functor[F[_]] {
    def map[A, B](f: A => B)(fa: F[A]): F[B]
  }
  object Functor {
    def apply[F[_]](implicit F: Functor[F]) = F
  }
  implicit class FunctorOps[F[_]: Functor, A](xs: F[A]) {
    def map[B](f: A => B): F[B] = Functor[F].map(f)(xs)
  }

  // Our List is a functor
  implicit val ListFunctor = new Functor[List] {
    def map[A, B](f: A => B)(fa: List[A]): List[B] = fa match {
      case Nil => Nil
      case Cons(hd, tl) => Cons(hd, f(tl))
    }
  }

  // fold: (F[A] => A) => Fix[F] => A
  def fold[F[_]: Functor, A](f: F[A] => A)(ff: Fix[F]): A =
    f(ff.out.map( fold[F, A](f) ))

  // unfold: (A => F[A]) => A => Fix[F]
  def unfold[F[_]: Functor, A](f: A => F[A])(a: A): Fix[F] = 
    Fix(f(a).map( unfold[F, A](f) ))
}

/* Sec 3. Sorting by Swapping */

object Sec3 {
  import Sec2._

  // The underlined sorted list in paper
  type StList[T] = List[T]
  val StNil = Nil
  val StCons = Cons

  // A sorting function transforms an unsorted list to a sorted list
  type SortFunc = Fix[List] => Fix[StList]

  // Angle 1: SortFunc is a fold that consumes a value of Fix[List]
  def c: List[Fix[StList]] => StList[List[Fix[StList]]] = ???
  def unfoldc: List[Fix[StList]] => Fix[StList] = unfold(c)
  def sort1: SortFunc = fold(unfold(c))

  def naiveInsert: List[Fix[StList]] => StList[List[Fix[StList]]] = {
    case Nil => StNil
    case Cons(x, Fix(StNil)) => StCons(x, Nil)
    case Cons(x, Fix(StCons(y, rest))) =>
      if (x <= y) StCons(x, Cons(y, rest))
      else        StCons(y, Cons(x, rest)) // Note: does not make use of the fact that y::rest is already sorted
  }

  def naiveInsertSort: Fix[List] => Fix[List] = fold(unfold(naiveInsert))

  // Angle 2: SortFunc is an unfold that produces a value of Fix[StList]
  def a: List[StList[Fix[List]]] => StList[Fix[List]] = ???
  def folda: Fix[List] => StList[Fix[List]] = fold(a)
  def sort2: SortFunc = unfold(fold(a))

  def bubble: List[StList[Fix[List]]] => StList[Fix[List]] = {
    case Nil => StNil
    case Cons(x, StNil) => StCons(x, Fix[List](Nil))
    case Cons(x, StCons(y, rest)) =>
      if (x <= y) StCons(x, Fix[List](Cons(y, rest)))
      else        StCons(y, Fix[List](Cons(x, rest)))
  }

  def bubbleSort: Fix[List] => Fix[StList] = unfold(fold(bubble))

  // naiveInsert and bubble only inspect elements in the first two levels
  // further generalize them to a `swap` function

  def swap[X]: List[StList[X]] => StList[List[X]] = {
    case Nil => StNil
    case Cons(a, StNil) => StCons(a, Nil)
    case Cons(a, StCons(b, rest)) =>
      if (a <= b) StCons(a, Cons(b, rest))
      else        StCons(b, Cons(a, rest))
  }

  // Now, redefine naiveInsertSort and bubbleSort using swap

  def naiveInsertSort2: Fix[List] => Fix[StList] =
    //fold[List, Fix[List]](unfold[List, List[Fix[List]]]
    fold(unfold({ a: List[Fix[StList]] =>
      swap[Fix[List]](a.map(_.out))
    }))

  def bubbleSort2: Fix[List] => Fix[List] =
    unfold(fold({ a: List[StList[Fix[List]]] =>
      swap[Fix[List]](a).map(Fix(_))
    }))

  def main(args: Array[String]): Unit = {
    println(naiveInsertSort(unsorted))
    println(bubbleSort(unsorted))

    println(naiveInsertSort2(unsorted))
    println(bubbleSort2(unsorted))
  }
}

/* Sec 4. Paramorphisms & Apomorphisms */

object Sec4 {
  import Sec2._
  import Sec3._

  // product of types
  type ⊗[A, B] = (A, B)
  // sum of types
  type ⊕[A, B] = Either[A, B]

  implicit class Fun1Ops[A, B](f: A => B) {
    def △[C](g: A => C): A => B ⊗ C = a => (f(a), g(a))
    def ▽[C](g: C => B): A ⊕ C => B = {
      case Left(a) => f(a)
      case Right(c) => g(c)
    }
  }

  // Examples
  def f: Int => Int = x => x + 1
  def g: Int => String = x => x.toString
  def h: Int => Int ⊗ String = f △ g

  def id[A]: A => A = a => a

  // Paramorphism
  def para[F[_]: Functor, A](f: F[Fix[F] ⊗ A] => A): Fix[F] => A = ff =>
    // id △ para(f): Fix[F] => (Fix[F] ⊗ A)
    f(ff.out.map(id △ para(f)))

  // Compute all proper suffixes of a list
  import scala.collection.immutable.{List => SList}
  def suf: List[Fix[List] ⊗ SList[Fix[List]]] => SList[Fix[List]] = {
    case Nil => SList()
    case Cons(n, (l, ls)) => l::ls
  }
  def suffixes: Fix[List] => SList[Fix[List]] = para(suf)

  // Define paramorphism using fold
  def para_alter[F[_]: Functor, A](f: F[Fix[F] ⊗ A] => A): Fix[F] => A = ff => {
    val g: F[(Fix[F], A)] => Fix[F] = ff => Fix[F](ff.map(_._1))
    fold(g △ f)(ff)._2
  }

  // Apomorphism ~ unfold, allows early termination of computation
  def apo[F[_]: Functor, A](f: A => F[Fix[F] ⊕ A]): A => Fix[F] = a =>
    // apo(f): A => Fix[F]
    // id ▽ apo(f): Fix[F] ⊕ A => Fix[F]
    Fix[F](f(a).map(id ▽ apo(f)))

  /* 4.1 */
}
