package types.alacarte

/*
sealed trait Expr[F[_]]
case class In[F[_]](t: F[Expr[F]]) extends Expr[F]

case class Val[E](i: Int)
case class Add[E](lhs: E, rhs: E)

sealed trait :+:[F[_], G[_], E]
case class Inl[F[_], G[_], E](t: F[E]) extends :+:[F, G, E]
case class Inr[F[_], G[_], E](t: G[E]) extends :+:[F, G, E]

object Expr {
  type IntExpr = Expr[Val]
  type AddExpr = Expr[Add]
  def e: Expr[:+:[Val, Add, ?]] = In(Inl[Val, Add, Int](Val[Int](1)))
}
*/
