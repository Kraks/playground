package compositional

// A concrete interpreter

import Expr._
import Stmt._

enum Value:
  case IntV(i: Int)

given Conversion[Int, Value] with
  def apply(i: Int): Value = IntV(i)

import Value._

type FunEnv = Map[String, FunDef]
type Store = Map[String, Value]

def evalOp(op: String, v1: Value, v2: Value): Value =
  val i1 = v1.asInstanceOf[IntV].i
  val i2 = v2.asInstanceOf[IntV].i
  op match {
    case "+" => i1 + i2
    case "-" => i1 - i2
    case "*" => i1 * i2
    case "/" => i1 / i2
    case "<" => if (i1 < i2) 1 else 0
    case ">" => if (i1 > i2) 1 else 0
    case "=" => if (i1 == i2) 1 else 0
    case _ => ???
  }

def eval(s: Expr, σ: Store)(using Γ: FunEnv): Value =
  s match {
    case Var(x) => σ(x)
    case Lit(i) => IntV(i)
    case BinOp(op, e1, e2) => evalOp(op, eval(e1, σ), eval(e2, σ))
    case Call(fname, args) => execFun(Γ(fname), args.map(eval(_, σ)))
  }

def exec(s: Stmt, σ: Store)(using Γ: FunEnv): (Option[Value], Store) =
  s match {
    case Skip => (None, σ)
    case Assign(x, e) => (None, σ + (x -> eval(e, σ)))
    case SSeq(s1, s2) =>
      exec(s1, σ) match {
        case (Some(v1), σ1) => (Some(v1), σ1)
        case (None, σ1) => exec(s2, σ1)
      }
    case Cond(e, s1, s2) =>
      val IntV(c) = eval(e, σ)
      if (c == 1) exec(s1, σ) else exec(s2, σ)
    case While(e, s) =>
      val IntV(c) = eval(e, σ)
      if (c == 1)
        exec(s, σ) match {
          case (Some(v), σ1) => (Some(v), σ1)
          case (None, σ1) => exec(While(e, s), σ1)
        }
      else (None, σ)
    case Ret(e) => (Some(eval(e, σ)), σ)
  }

def execFun(fdef: FunDef, vs: List[Value])(using Γ: FunEnv): Value =
  val FunDef(_, params, body) = fdef
  val (Some(ret), σ) = exec(body, params.zip(vs).toMap)
  ret

def run(p: Program, entrance: String, args: Value*): Value =
  given funEnv: FunEnv = p.funEnv
  execFun(funEnv(entrance), args.toList)
