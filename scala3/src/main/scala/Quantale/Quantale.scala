package quantale

trait SemiLattice[T]:
  extension (x: T)
    def ⊔(y: T): T 

trait Monoid[T]:
  def I: T
  extension (x: T)
    def ▷(y: T): T

trait EffQuantale[T] extends SemiLattice[T] with Monoid[T]

given ProductEffectQuantale[E1: EffQuantale, E2: EffQuantale]: EffQuantale[(E1, E2)] with
  val e1 = summon[EffQuantale[E1]]
  val e2 = summon[EffQuantale[E2]]
  def I: (E1, E2) = (e1.I, e2.I)
  extension (x: (E1, E2))
    def ⊔(y: (E1, E2)): (E1, E2) = (x._1 ⊔ y._1, x._2 ⊔ y._2)
    def ▷(y: (E1, E2)): (E1, E2) = (x._1 ▷ y._1, x._2 ▷ y._2)

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

