package types.pattern

sealed trait Maybe[A]
final case class Just[A](x: A) extends Maybe[A]
final case class Empty[A]()    extends Maybe[A]

sealed trait \/[A, B]
final case class -\/[A, B](x: A) extends \/[A, B]
final case class \/-[A, B](x: A) extends \/[A, B]

object Either {
  type Either[A, B] = A \/ B
}
import Either._

sealed trait Validation[A, B]
final case class Failure[A, B](x: A) extends Validation[A, B]
final case class Success[A, B](x: B) extends Validation[A, B]

/* Semigroup, Monoid */

trait Semigroup[A] {
  def append(a1: A, a2: A): A
}

// Associativity law:
// append(a1, append(a2, a3)) == append(append(a1, a2), a3)

trait Monoid[A] extends Semigroup[A] {
  def zero: A
}

// Identity:
// append(a, zero) == a

/* Functors */

trait Functor[F[_]] {
  def map[A, B](fa: F[A])(ab: A => B): F[B]
}

// Identity:
// map(fa)(identity) == fa
// Composition
// map(map(fa)(ab))(bc) == map(fa)(ab.andThen(bc)) == map(fa)(x => bc(ab(x)))

/* Natural transformation */

trait NaturalTransformation[-F[_], +G[_]] {
  def apply[A](fa: F[A]): G[A]
}
object NaturalTransformation {
  type ~> [-F[_], G[_]] = NaturalTransformation[F, G]
}
import NaturalTransformation._

/* Functor composition */

// Natural composition of two functors

case class Composite[F[_], G[_], A](run: F[G[A]])

// Product of two functors is a functor

case class Product[F[_], G[_], A](run: (F[A], G[A]))

// Coproduct (sum) of two functors is a functor

case class Coproduct[F[_], G[_], A](run: Either[F[A], G[A]])

/* Lifting */
// e.g., x to List(x)

/* Apply: a way of applying a lifted function F[A => B] to a lifted value F[A] to yield F[B]. */

trait Apply[F[_]] extends Functor[F] {
  def ap[A, B](fa: F[A])(fab: F[A => B]): F[B]
}

// Associative composition:
// ap(ap(fa)(fab))(fbc) == ap(fa)(ap(fab)(map(fbc)(_.compose(_).curry))

/* Applicative: provides the ability to lift any value into a functor */

trait Applicative[F[_]] extends Apply[F] {
  def point[A](a: A): F[A]
}

// Identity:
//   ap(fa)(point) == fa
// Homomorphism:
//   ap(point(a))(point(ab)) == point(ab(a))
// Interchange:
//   ap(point(a))(fab) == ap(fab)(point(_.apply(a)))
// Derived map:
//   map(fa)(ab) == ap(fa)(point(ab))

/* Bind */

trait Bind[F[_]] extends Apply[F] {
  def bind[A, B](fa: F[A])(afb: A => F[B]): F[B]
}

// Associative bind:
//   bind(bind(fa)(afb))(bfc) == bind(fa)(a => bind(afb(a))(fbc))
// Derived ap:
//   ap(fa)(fab) == bind(fab)(map(fa)(_))

/* Monad */

trait Monad[F[_]] extends Applicative[F] with Bind[F]

// Right identity:
//   bind(fa)(point(_)) == fa
// Left identity:
//   bind(point(a))(afb) == afb(a)

/* Invariant functors */

trait InvariantFunctor[F[_]] {
  def xmap[A, B](ma: F[A], f: A => B, g: B => A): F[B]
}

/* Contravariant */

trait Contravariant[F[_]] extends InvariantFunctor[F] {
  def contramap[A, B](r: F[A])(f: B => A): F[B]
}

/* Bifunctor */

trait Bifunctor[F[_, _]] {
  def bimap[A, B, C, D](fab: F[A, B])(f: A => C, g: B => D): F[C, D]
}

/* Profunctor */

trait Profunctor[P[_, _]] {
  def dimap[A, B, C, D](fab: P[A, B])(f: C => A)(g: B => D): P[C, D]
}

/* Foldable */

trait Foldable[F[_]] {
  def foldMap[A, B](fa: F[A])(f: A => B)(implicit F: Monoid[B]): B
  def foldRight[A, B](fa: F[A], z: => B)(f: (A, => B) => B): B
}

// Consisttent left fold:
//   foldMap(fa)(Vector(_)) == foldLeft(fa, Vector.empty[A])(_ :+ _)
// Consisttent right fold:
//   foldMap(fa)(Vector(_)) == foldRight(fa, Vector.empty[A])(_ +: _)

/* Traversable */

trait Traverse[F[_]] extends Functor[F] with Foldable[F] {
  final def sequence[G[_]: Applicative, A](fga: F[G[A]]): G[F[A]] = ???
}

/* Natural numbers */

trait Natural { self =>
  def fold[Z](zero: => Z, succ: Z => Z): Z
  def succ: Natural = new Natural {
    def fold[Z](zero: => Z, succ: Z => Z): Z = succ(self.fold(zero, succ))
  }
  def +(that: Natural): Natural = new Natural {
    def fold[Z](zero: => Z, succ: Z => Z): Z = that.fold[Natural](self, _.succ).fold[Z](zero, succ)
  }
  def *(that: Natural): Natural = new Natural {
    def fold[Z](zero: => Z, succ: Z => Z): Z = that.fold[Natural](Natural.zero, _ + self).fold[Z](zero, succ)
  }
  def isZero: Boolean = fold[Boolean](true, _ => false)
  def toInt: Int = fold[Int](0, _ + 1)
  override def toString = toInt.toString
}
object Natural {
  val zero = new Natural {
    def fold[Z](zero: => Z, succ: Z => Z):Z = zero
  }
  def of(v: Int): Natural = if (v == 0) zero else of(v-1).succ
}

/* Optics */

/* Lenses provide a way to focus on a single term inside a product */

abstract class PLens[S, T, A, B] extends Serializable { self => 
  def get(s: S): A
  def set(b: B): S => T
  def modifyF[F[_]: Functor](f: A => F[B])(s: S): F[T]
  def modify(f: A => B): S => T
}
object Lens {
  type Lens[S, A] = PLens[S, S, A, A]
}

/* Prisms provide a way to focus on a single term inside a coproduct (sum) */

abstract class PPrism[S, T, A, B] extends Serializable { self =>
  def getOrModify(s: S): T \/ A
  def reverseGet(b: B): T
  def getOption(s: S): Option[A]
}
object Prism {
  type Prism[S, A] = PPrism[S, S, A, A]
}

/* Traversals provide a way to focus on zero or more elements */

abstract class PTraversal[S, T, A, B] extends Serializable { self =>
  def modifyF[F[_]: Applicative](f: A => F[B])(s: S): F[T]
}
object Traversable {
  type Traversable[S, A] = PTraversal[S, S, A, A]
}

/* Folds provide a way to fold over zero or more values in a larger structure */

abstract class Fold[S, A] extends Serializable { self =>
  def foldMap[M: Monoid](f: A => M)(s: S): M
}

/* Getters provide a way to get a part of a larger structure */

abstract class Getter[S, A] extends Serializable { self =>
  def get(s: S): A
}

/* Setters provide a way to modify and set a part of a larget structure */

abstract class PSetter[S, T, A, B] extends Serializable { self =>
  def modify(f: A => B): S => T
  def set(b: B): S => T
}
object Setter {
  type Setter[S, A] = PSetter[S, S, A, A]
}

/* Isos provide an isomorphism between an A in S and a B in T */

abstract class PIso[S, T, A, B] extends Serializable { self =>
  def get(s: S): A
  def reverseGet(b: B): T
  def reverse: PIso[B, A, T, S]
}
object Iso {
  type Iso[S, A] = PIso[S, S, A, A]
}

/* Optionals provide either a way to get an A in S, or to get a T, and a way to set a B in S to get a T. */

abstract class POptional[S, T, A, B] extends Serializable { self =>
  def getOrModify(s: S): T \/ A
  def set(b: B): S => T
  def getOption(s: S): Option[A]
  def modifyF[F[_]: Applicative](f: A => F[B])(s: S): F[T]
  def modify(f: A => B): S => T
}
object Optional {
  type Optional[S, A] = POptional[S, S, A, A]
}
