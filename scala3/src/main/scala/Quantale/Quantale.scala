package quantale

import scala.annotation.StaticAnnotation

/* Algebras */

trait SemiLattice[T]:
  extension (x: T)
    def ⊔(y: T): T

trait Monoid[T]:
  def I: T
  extension (x: T)
    def ▷(y: T): T

trait EffQuantale[T] extends SemiLattice[T] with Monoid[T]

trait IterEffQuantale[T: EffQuantale]:
  extension (x: T)
    def *(): T

given ProductEffectQuantale[E1: EffQuantale, E2: EffQuantale]: EffQuantale[(E1, E2)] with
  val e1 = summon[EffQuantale[E1]]
  val e2 = summon[EffQuantale[E2]]
  def I: (E1, E2) = (e1.I, e2.I)
  extension (x: (E1, E2))
    def ⊔(y: (E1, E2)): (E1, E2) = (x._1 ⊔ y._1, x._2 ⊔ y._2)
    def ▷(y: (E1, E2)): (E1, E2) = (x._1 ▷ y._1, x._2 ▷ y._2)

/* Annotation */

class Eff[E: EffQuantale](e: E) extends StaticAnnotation

class AbsEff[E: EffQuantale]() extends StaticAnnotation

class IterEff[E: EffQuantale : IterEffQuantale](e: E) extends StaticAnnotation

/* Flanagan and Qadeer’s Atomicity */

enum Atomicity:
  case B, L, R, A, ⊤

given AtomicityQuantale: EffQuantale[Atomicity] with
  import Atomicity._
  def I: Atomicity = B
  extension (x: Atomicity)
    def ⊔(y: Atomicity): Atomicity = (x, y) match {
      case (B, y) => y
      case (y, B) => y
      case (R, L)
         | (L, R) => A
      case (A, R)
         | (R, A) => A
      case (A, L)
         | (L, A) => A
      case (_, ⊤)
         | (⊤, _) => ⊤
    }
    def ▷(y: Atomicity): Atomicity = (x, y) match {
      case (B, y) => y
      case (R, B) => R
      case (R, L) => A
      case (R, R) => R
      case (R, A) => A
      case (R, ⊤) => ⊤
      case (L, B)
         | (L, L) => L
      case (L, _) => ⊤
      case (A, B)
         | (A, L) => A
      case (A, _) => ⊤
      case (⊤, _) => ⊤
    }

given IterAtomicityQuantale: IterEffQuantale[Atomicity] with
  import Atomicity._
  extension (x: Atomicity)
    def *(): Atomicity = x match {
      case A => ⊤
      case _ => x
    }

trait AtomicityOp {
  import Atomicity._
  type Lock
  type eff = Eff[Atomicity]
  @eff(B) def newLock: Unit
  @eff(R) def acquire(l: Lock): Unit
  @eff(L) def release(l: Lock): Unit
  // TODO: alloc/read/write
}

/* Finite Trace Effect */

given FinTraceQuantale[T: Monoid]: EffQuantale[Set[T]] with
  def I: Set[T] = Set(summon[Monoid[T]].I)
  extension (x: Set[T])
    def ⊔(y: Set[T]): Set[T] = x ++ y
    def ▷(y: Set[T]): Set[T] = for { a <- x; b <- y } yield a ▷ b

/* Test */

object EffQuantaleTest {
  import Atomicity._

  @Eff[Atomicity](B) def pure(x: Int): Int = x+1

  // @Eff[E](?) def map[A, B, E: EffQuantale](xs: List[A])(f: A => B @Eff[E]): List[B]

  /*
  def f(x: ((A => B @Eff[Atomicity](R)) @Eff)) = {
    pure(x)
    var y: Int = 0
    val z = f(...)
    g(z)

    // XXX: how to annotate while loop?
    // @Eff[Atomicity](B) while (y < 10) { y = y + 1 }
  }
  */

  def main(args: Array[String]): Unit = {
  }
}
