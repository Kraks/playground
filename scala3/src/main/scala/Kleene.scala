package kleene

// Scala translation of A Very General Method of Computing Shortest Paths
// Haskell version:
// http://r6.ca/blog/20110808T035622Z.html

/* Laws
 * add comm: a + b = b + a
 * add assoc: (a + b) + c = a + (b + c)
 * add id: a + 0 = 0 + a = a
 * mul assoc: (a * b) * c = a * (b * c)
 * mul id: a * 1 = 1 * a = a
 * annihilation: a * 0 = 0 * a = 0
 * distr: a * (b + c) = a * b + a * c
 *        (a + b) * c = a * c + b * c
 */

trait Semiring[T]:
  def zero: T
  def one: T
  extension (x: T)
    def +(y: T): T
    def *(y: T): T

def sum[T: Semiring](xs: List[T]): T =
  xs.foldLeft(summon[Semiring[T]].zero)(_ + _)

def prod[T: Semiring](xs: List[T]): T =
  xs.foldLeft(summon[Semiring[T]].one)(_ * _)

/* Laws
 * a★ = 1 + a * a★ = 1 + a★ * a
 * a + a = a
 * a * x + x = x ⇒ a★ * x + x = x
 * x * a + x = x ⇒ x * a★ + x = x
 */

// Or *-semiring
trait Kleene[T] extends Semiring[T]:
  extension (x: T)
    def ★(): T
    def ⊕(): T = x * x.★()

/* Square Matrix (Mₙ, +, ∙, 0, 1)
 * Mₙ the set of all n × n matrices
 * +  the usual matrix addition
 * ∙  the usual matrix multiplication
 * 0  the zero matrix
 * 1  the identity matrix
 */

case class Edge[I](from: I, to: I)

case class Matrix[T, E](m: Map[Edge[T], E])

//def buildMatrix[T, E](f: Edge[T] => E): Matrix[T, E]
