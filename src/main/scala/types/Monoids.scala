package types

object Monoids {
  trait Monoid[A] {
    /* Associativity: ∀ a b c, op(op(a, b), c) = op(a, op(b, c)). */
    def op(a1: A, a2: A): A
    /* Identity element: ∀ a, op(id, a) = op(a, id) = a. */
    def id: A
  }

  object Monoid {
    def apply[A](implicit m: Monoid[A]): Monoid[A] = m
  }

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

  def optionMonoid[A: Monoid] = new Monoid[Option[A]] {
    def op(a1: Option[A], a2: Option[A]) = (a1, a2) match {
      case (Some(v1), Some(v2)) => Some(Monoid[A].op(v1, v2))
      case (Some(v1), _) => Some(Monoid[A].op(v1, Monoid[A].id))
      case (_, Some(v2)) => Some(Monoid[A].op(Monoid[A].id, v2))
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

  def foldMap[A, B](as: List[A], m: Monoid[B])(f: A => B): B =
    as.foldLeft(m.id)((acc, x) => m.op(acc, f(x)))
}

