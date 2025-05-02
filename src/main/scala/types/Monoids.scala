package types

trait Semigroup[A] {
  /* Associativity: ∀ a b c, op(op(a, b), c) = op(a, op(b, c)). */
 def op(a1: A, a2: A): A
}

object Semigroup {
  def apply[A](implicit s: Semigroup[A]): Semigroup[A] = s
}

trait Monoid[A] extends Semigroup[A] {
  /* Identity element: ∀ a, op(id, a) = op(a, id) = a. */
 def id: A
}

object Monoid {
  def apply[A](implicit m: Monoid[A]): Monoid[A] = m
}

object Monoids {
  def stringMonoid = new Monoid[String] {
    def op(a1: String, a2: String) = a1 + a2
    def id = ""
  }

  def listMonoid[A] = new Monoid[List[A]] {
    def op(a1: List[A], a2: List[A]) = a1 ++ a2
    def id = Nil
  }

  /* Exercise 10.1 */

  def intAdd = new Monoid[Int] {
    def op(a1: Int, a2: Int) = a1 + a2
    def id = 0
  }

  def intMul = new Monoid[Int] {
    def op(a1: Int, a2: Int) = a1 * a2
    def id = 1
  }

  def boolOr = new Monoid[Boolean] {
    def op(a1: Boolean, a2: Boolean) = a1 || a2
    def id = false
  }

  def boolAnd = new Monoid[Boolean] {
    def op(a1: Boolean, a2: Boolean) = a1 && a2
    def id = true
  }

  /* Exercise 10.2 */

  def optionMonoid[A: Semigroup] = new Monoid[Option[A]] {
    def op(a1: Option[A], a2: Option[A]) = (a1, a2) match {
      case (Some(v1), Some(v2)) => Some(Semigroup[A].op(v1, v2))
      case (Some(v1), _) => Some(v1)
      case (_, Some(v2)) => Some(v2)
      case (_, _) => None
    }
    def id = None
  }

  def dual[A](m: Monoid[A]): Monoid[A] = new Monoid[A] {
    def op(x: A, y: A): A = m.op(y, x)
    def id = m.id
  }

  /* Exercise 10.3 */

  def endoMonoid[A] = new Monoid[A => A] {
    def op(f: A => A, g: A => A) = f compose g
    def id = (a) => a
  }

  def concatenate[A](as: List[A], m: Monoid[A]): A =
    as.foldLeft(m.id)(m.op)

  /* Exercise 10.5 */

  def foldMap[A, B](as: List[A], m: Monoid[B])(f: A => B): B =
    as.foldLeft(m.id)((acc, x) => m.op(acc, f(x)))

  /* Exercise 10.6 */

  def foldMap_[A, B](as: List[A], m: Monoid[B])(f: A => B): B =
    as.foldRight(m.id)((x, acc) => m.op(acc, f(x)))

  def foldRight[A, B](as: List[A])(acc: B)(f: (A, B) => B): B =
    foldMap(as, endoMonoid[B])(f.curried)(acc)

  def foldLeft[A, B](as: List[A])(acc: B)(f: (B, A) => B): B =
    foldMap(as, dual(endoMonoid[B]))(a => b => f(b, a))(acc)

  /* Exercise 10.7 */

  def foldMapV[A, B](v: IndexedSeq[A], m: Monoid[B])(f: A => B): B =
    if (v.length == 0) m.id
    else if (v.length == 1) f(v(0))
    else {
      val (l, r) = v.splitAt(v.length / 2)
      m.op(foldMapV(l, m)(f), foldMapV(r, m)(f))
    }

  /* Exercise 10.8 */

  /* TODO */

  /* Exercise 10.9 */

  def isOrdered(xs: IndexedSeq[Int]): Boolean = {
    val m = new Monoid[(Option[Int], Boolean)] {
      def op(a1: (Option[Int], Boolean), a2: (Option[Int], Boolean)) = {
        (a1, a2) match {
          //Note: this assumes fold from left.
          case ((Some(x), b1), (Some(y), b2)) => (Some(y), (x<=y) && b1 && b2)
          case ((None, _), a2) => a2
          case (a1, (None, _)) => a1
        }
      }
      def id = (None, true)
    }
    foldMap(xs.toList, m)(i => (Some(i), true))._2
  }

  def main(args: Array[String]) {
    println(isOrdered(Array(1,2,3,4,4)))
    println(isOrdered(Array(1,2,3,4,5).reverse))
    println(isOrdered(Array(1,1,1,1,1)))
    println(isOrdered(Array(1,1,0,1,1)))
  }
}

