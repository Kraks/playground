package tmp

trait SemiGroup[T]:
  extension (x: T)
    def ++(y: T): T

trait Monoid[T] extends SemiGroup[T]:
  def unit: T

trait Functor[F[_]]:
  extension [A, B](x: F[A])
    def map(f: A => B): F[B]

trait Monad[M[_]] extends Functor[M]:
  def pure[A](x: A): M[A]
  extension [A](m: M[M[A]])
    def join: M[A] = m.flatMap(x => x)
  extension [A, B](m: M[A])
    def flatMap(f: A => M[B]): M[B]
    def map(f: A => B): M[B] = m.flatMap(f.andThen(pure))

trait Comonad[W[_]] extends Functor[W]:
  extension [A, B](w: W[A])
    def extract: A
    def extend(f: W[A] => B): W[B]
    def duplicate: W[W[A]] = w.extend(x => x)
    def map(f: A => B): W[B] = w.extend(wa => f(wa.extract))
    // or, alternatively define `extend` as `duplicate.map(f)` and leave duplicate abstract

/* A few comonad examples */

// Id comonad

type Id[A] = A

given idComonad: Comonad[Id] with
  extension [A, B](w: Id[A])
    def extract: A = w
    def extend(f: Id[A] => B): Id[B] = f(w)

// Cofree

case class Cofree[F[_]: Functor, A](extract: A, sub: F[Cofree[F, A]])

given cofreeComonad[F[_]: Functor]: Comonad[[A] =>> Cofree[F, A]] with
  extension [A, B](cf: Cofree[F, A])
    def extract: A = cf.extract
    def extend(f: Cofree[F, A] => B): Cofree[F, B] =
      Cofree(f(cf), cf.sub.map(_.extend(f)))

// Coreader

case class Coreader[R, A](extract: A, ask: R)

given coreaderComonad[R]: Comonad[[A] =>> Coreader[R, A]] with
  extension [A, B](w: Coreader[R, A])
    def extract: A = w.extract
    def extend(f: Coreader[R, A] => B): Coreader[R, B] = Coreader(f(w), w.ask)

// Cowriter

case class Cowriter[W: Monoid, A](tell: W => A)

given cowriterComonad[W: Monoid]: Comonad[[A] =>> Cowriter[W, A]] with
  extension [A, B](w: Cowriter[W, A])
    def extract: A = w.tell(summon[Monoid[W]].unit)
    def extend(f: Cowriter[W, A] => B): Cowriter[W, B] =
      Cowriter(w1 => f(Cowriter(w2 => w.tell(w1 ++ w2))))

// Stream

trait Stream[A](val hd: A):
  def tl: Stream[A]

given streamComonad: Comonad[Stream] with
  extension [A, B](s: Stream[A])
    def extract: A = s.hd
    def extend(f: Stream[A] => B): Stream[B] =
      new Stream[B](f(s)) { def tl: Stream[B] = s.tl.extend(f) }
    /* optional:
    override def duplicate: Stream[Stream[A]] =
      new Stream(s) { def tl: Stream[Stream[A]] = s.tl.duplicate }
    override def map(f: A => B): Stream[B] =
      new Stream(f(s.hd)) { def tl: Stream[B] = s.tl.map(f) }
    */

def generate[A](f: A => A, init: A): Stream[A] =
  new Stream(init) { def tl = generate(f, init).extend(s => f(s.extract)) }

def nats: Stream[Int] = generate(_ + 1, 0)

extension (s: Stream[Int])
  def windowSum(n: Int): Int =
    if (n == 1) s.hd
    else s.hd + s.tl.windowSum(n-1)

def tensWindow: Stream[Int] = nats.extend(_.windowSum(10))

// Adjunction

trait Adjunction[F[_],  G[_]]:
  def left[A, B](f: F[A] => B): A => G[B]
  def right[A, B](f: A => G[B]): F[A] => B

// an adjunction inducies a monad and a comonad
extension [F[_]: Functor, G[_]: Functor](adj: Adjunction[F, G])
  def monad: Monad[[X] =>> G[F[X]]] = new Monad[[X] =>> G[F[X]]]:
    def pure[A](a: A): G[F[A]] = adj.left((x: F[A]) => x)(a)
    extension [A, B](m: G[F[A]])
      def flatMap(f: A => G[F[B]]): G[F[B]] = summon[Functor[G]].map(m)(adj.right(f))
          //m.map[F[A], F[B]](adj.right(f))
  def comonad: Comonad[[X] =>> F[G[X]]] = new Comonad[[X] =>> F[G[X]]]:
    extension [A, B](w: F[G[A]])
      def extract: A = adj.right((x: G[A]) => x)(w)
      def extend(f: F[G[A]] => B): F[G[B]] = summon[Functor[F]].map(w)(adj.left(f))

// curried functions and tupled functions are dual to each other
given homSetAdj[R]: Adjunction[[X] =>> (X, R), [X] =>> (R => X)] with
  def left[A, B](f: ((A, R)) => B): A => R => B =
    Function.untupled(f).curried
  def right[A, B](f: A => R => B): ((A, R)) => B =
    Function.uncurried(f).tupled

given tupleFunctor[R]: Functor[[X] =>> (X, R)] with
  extension [A, B](x: (A, R))
    def map(f: A => B): (B, R) = (f(x._1), x._2)

given funcFunctor[R]: Functor[[X] =>> (R => X)] with
  extension [A, B](x: R => A)
    def map(f: A => B): R => B = r => f(x(r))

object TmpTest {
  def main(args: Array[String]): Unit = {
    // Σ [0, 9]
    assert(nats.windowSum(10) == 45)
    // Σ [3, 12]
    println(nats.tl.tl.tl.windowSum(10))

    println(tensWindow.hd)
    println(tensWindow.tl.hd)
    println(tensWindow.tl.tl.hd)

    val adj: Adjunction[[X] =>> (X, Int), [X] =>> (Int => X)] = homSetAdj[Int]
    val stateMon: Monad[[X] =>> Int => (X, Int)] = adj.monad
    val costateCom: Comonad[[X] =>> (Int => X, Int)] = adj.comonad
  }
}
