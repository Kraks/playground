package compositional

// An abstract interpreter

import Expr._
import Stmt._

type AbsValue = Interval
type AbsStore = Map[String, AbsValue]

def absEvalOp(op: String, i1: AbsValue, i2: AbsValue): AbsValue =
  op match {
    case "+" => i1 + i2
    case "-" => i1 - i2
    case "*" => i1 * i2
    case "/" => i1 / i2
    case "<" =>
      if (i1.ub < i2.lb) Interval.from(1)
      else if (i1.lb > i2.ub) Interval.from(0)
      else Interval.from(0, 1)
    case ">" =>
      if (i1.lb > i2.ub) Interval.from(1)
      else if (i1.ub < i2.lb) Interval.from(0)
      else Interval.from(0, 1)
    case "=" =>
      if (i1.toConst == i2.toConst) Interval.from(1)
      else Interval.from(0, 1)
    case _ => ???
  }

def absEval(s: Expr, σ: AbsStore)(using Γ: FunEnv): AbsValue =
  s match {
    case Var(x) => σ(x)
    case Lit(i) => Interval.from(i)
    case BinOp(op, e1, e2) => absEvalOp(op, absEval(e1, σ), absEval(e2, σ))
    case Call(fname, args) => absExecFun(Γ(fname), args.map(absEval(_, σ)))
  }

def absExec(s: Stmt, σ: AbsStore)(using Γ: FunEnv): (Option[AbsValue], AbsStore) =
  s match {
    case Skip => (None, σ)
    case Assign(x, e) => (None, σ ⊔ Map(x -> absEval(e, σ)))
    case SSeq(s1, s2) =>
      absExec(s1, σ) match {
        case (Some(v1), σ1) => (Some(v1), summon[Lattice[AbsStore]].bot) ⊔ absExec(s2, σ1)
        case (None, σ1) => absExec(s2, σ1)
      }
    case Cond(e, s1, s2) =>
      val c = absEval(e, σ)
      val thn = if (Interval.from(1) ⊑ c) Some(absExec(s1, σ)) else None
      val els = if (Interval.from(0) ⊑ c) Some(absExec(s2, σ)) else None
      (thn ⊔ els).get
    case While(e, s) => 
      val c = absEval(e, σ)
      ???
/*
      val IntV(c) = eval(e, σ)
      if (c == 1)
        exec(s, σ) match {
          case (Some(v), σ1) => (Some(v), σ1)
          case (None, σ1) => exec(While(e, s), σ1)
        }
      else (None, σ)
 */
    case Ret(e) => (Some(absEval(e, σ)), σ)
  }

def absExecFun(fdef: FunDef, vs: List[AbsValue])(using Γ: FunEnv): AbsValue =
  val FunDef(_, params, body) = fdef
  val (Some(ret), σ) = absExec(body, params.zip(vs).toMap)
  ret
