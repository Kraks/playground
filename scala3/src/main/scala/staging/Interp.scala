package staging.interp

import scala.quoted.*

enum Term:
  case Lit(i: Int)
  case BinOp(op: String, e1: Term, e2: Term)
  case Var(x: String)
  case App(t1: Term, t2: Term)
  case Lam(x: String, t: Term)

package unstaged {
enum Value:
  case IntV(i: Int)
  case ClosureV(x: String, t: Term, env: Env)

type Env = Map[String, Value]

import Term._
import Value._

def eval(t: Term, env: Env): Value =
  t match
    case Lit(i) => IntV(i)
    case BinOp("+", e1, e2) =>
      (eval(e1, env), eval(e2, env)) match
        case (IntV(v1), IntV(v2)) => IntV(v1 + v2)
        case _ => throw new RuntimeException("integers expected")
    case Var(x) => env(x)
    case Lam(x, e) => ClosureV(x, e, env)
    case App(t1, t2) =>
      (eval(t1, env), eval(t2, env)) match
        case (ClosureV(x, body, env1), v) =>
          eval(body, env1 + (x -> v))
        case _ => throw new RuntimeException("closure expected")
}

package staged {
enum Value:
  case IntV(i: Int)
  case FunV(f: Value => Value)

type Env = Map[String, Value]

import Term._
import Value._

def later[T: Type, U: Type](f: Expr[T] => Expr[U])(using Quotes): Expr[T => U] =
  '{ (x: T) => ${ f('x) } }

def now[T: Type, U: Type](f: Expr[T => U])(using Quotes): Expr[T] => Expr[U] =
  (x: Expr[T]) => '{ $f($x) }

given ToExpr[Term] with
  def apply(t: Term)(using Quotes): Expr[Term] =
    import quotes.reflect.*
    t match
      case Lit(i) => '{ Lit(${Expr(i)}) }
      case BinOp(op, e1, e2) => '{ BinOp(${Expr(op)}, ${Expr(e1)}, ${Expr(e2)}) }
      case Var(x) => '{ Var(${Expr(x)}) }
      case Lam(x, e) => '{ Lam(${Expr(x)}, ${Expr(e)}) }
      case App(t1, t2) => '{ App(${Expr(t1)}, ${Expr(t2)}) }

given FromExpr[Term] with
  def unapply(t: Expr[Term])(using Quotes): Option[Term] =
    import quotes.reflect.*
    t match
      case '{ Lit(${Expr(i)}) } => Some(Lit(i))
      case '{ BinOp(${Expr(op)}, ${Expr(e1)}, ${Expr(e2)}) } => Some(BinOp(op, e1, e2))
      case '{ Var(${Expr(x)}) } => Some(Var(x))
      case '{ Lam(${Expr(x)}, ${Expr(e)}) } => Some(Lam(x, e))
      case '{ App(${Expr(t1)}, ${Expr(t2)}) } => Some(App(t1, t2))
      case _ => None

def eval(t: Term, env: Expr[Env])(using Quotes): Expr[Value] =
  t match
    case Lit(i) => '{ IntV(${Expr(i)}) }
    /*
    One wrong way is to use the following code. The pattern matching
    inspects the code returned by eval at compile time, but we want to
    inspect the code at runtime.
    case BinOp("+", e1, e2) =>
      (eval(e1, env), eval(e2, env)) match
        case ('{ IntV($v1) }, '{ IntV($v2) }) => '{ IntV($v1 + $v2) }
        case _ => throw new RuntimeException("compile-time error: integers expected")
    */
    case BinOp("+", e1, e2) => '{
      (${eval(e1, env)}, ${eval(e2, env)}) match
        case (IntV(v1), IntV(v2)) => IntV(v1 + v2)
        //case _ => throw new RuntimeException("integers expected")
      }
    case Var(x) => '{ ${env}(${Expr(x)}) }
    case Lam(x, e) =>
      val f: Expr[Value] => Expr[Value] = (v: Expr[Value]) => eval(e, '{ ${env} + (${Expr(x)} -> $v) })
      '{ FunV(${later(f)}) }
    case App(t1, t2) => '{
      (${eval(t1, env)}, ${eval(t2, env)}) match
        case (FunV(f), v) => f(v)
        //case _ => throw new RuntimeException("closure expected")
      }

given staging.Compiler = staging.Compiler.make(this.getClass.getClassLoader)
def specEval(e: Term): Env => Value = staging.run {
  val stagedEval: Expr[Env => Value] =
    '{ (env: Env) => ${eval(e, 'env)} }
  println(stagedEval.show)
  stagedEval
}

@main def main: Unit = {
  /*
  val ex1 = BinOp("+", Lit(1), Lit(2))
  val ex1Code = specEval(ex1)
  assert(ex1Code(Map.empty) == IntV(3))

  val ex2 = Var("x")
  val ex2Code = specEval(ex2)
  assert(ex2Code(Map("x" -> IntV(3))) == IntV(3))
  */
  val ex3 = App(App(Lam("y", Lam("x", BinOp("+", Var("x"), Var("y")))), Lit(3)), Lit(4))
  val ex3Code = specEval(ex3)
  assert(ex3Code(Map.empty) == IntV(7))

  /*
  val ex4 = {
    val f = Lam("x", BinOp("+", Lit(1), Var("x")))
    App(App(Lam("x", Lam("f", App(Var("f"), Var("x")))), Lit(4)), f)
  }
  val ex4Code = specEval(ex4)
  */
  //println(ex4Code(Map.empty))
}

}
