package types.sc

object AST {
  type Name = String

  abstract class Expr
  case class Var(x: Name) extends Expr
  case class Ctr(x: Name, es: List[Expr]) extends Expr
  case class FCall(x: Name, es: List[Expr]) extends Expr
  case class GCall(x: Name, es: List[Expr]) extends Expr
  case class Let(x: Name, e: Expr, body: Expr) extends Expr

  case class Pat(p: Name, ps: List[Name])

  case class GDef(x: Name, p: Pat, ns: List[Name], body: Expr)
  case class FDef(x: Name, ns: List[Name], body: Expr)

  case class Program(fs: List[FDef], gs: List[GDef])

  type Renaming = List[(Name, Name)]
  type Subst = List[(Name, Expr)]
  type NameSupply = List[Name]

  type Conf = Expr
  type Value = Expr
  type Task = (Conf, Program)
  type Env = List[(Name, Value)]

  case class Contract(x: Name, p: Pat)

  abstract class Step[T]
  case class Stop() extends Step[Nothing]
  case class Transient[T](t: T) extends Step[T]
  case class Variants[T](vs: List[(Contract, T)]) extends Step[T]
  case class Decompose[T](cs: List[T]) extends Step[T]
  case class Fold[T](t: T, rn: Renaming) extends Step[T]

  abstract class Graph[T]
  case class Node[T](t: T, s: Step[Graph[T]]) extends Graph[T]

  type Tree[T] = Graph[T]
  type TNode[T] = Tree[T]

  type Machine[T] = NameSupply => T => Step[T]
}
