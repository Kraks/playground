package types

/*
sealed trait Free[F[_], A]
case class Return[F[_], A](a: A) extends Free[F, A]
case class Suspend[F[_], A](s: F[Free[F, A]]) extends Free[F, A]

object IO {
  type IO[F[_], A] = Free[({type λ[α] = (F[I], I => α) forSome {type I}})#λ, A]
}

trait Yoneda[F[_], A] {
  def map[B](f: A => B): F[B]
}
*/
