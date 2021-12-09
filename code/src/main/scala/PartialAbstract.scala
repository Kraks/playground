package compositional

// Author: Guannan Wei <guannanwei@purdue.edu>
// A ``multi-stage'' abstract interpreter that can generate code
// for analyzing currently unknown functions.

import Expr._
import Stmt._

case class Sym(x: Int)
case class Op(rand: String, rators: List[Any])
case class Let(x: String, e: Op)

enum AbsValCode:
  case AbsIntV(i: Interval)
  case Code(x: Sym)

import AbsValCode._

given Conversion[Interval, AbsValCode] with
  def apply(i: Interval): AbsValCode = AbsIntV(i)

object Stage {
  var stFresh = 0
  var stBlock: List[Let] = Nil
  def run[A](f: => A): A = {
    val sF = stFresh
    val sB = stBlock
    try f finally { stFresh = sF; stBlock = sB }
  }

  def fresh: Sym = { stFresh += 1; Sym(stFresh-1) }
  def reflect(s: Op): Sym =
    val Sym(x) = fresh
    stBlock = stBlock :+ Let("x"+x, s)
    Sym(x)
  def reify(f: => Op): Op = ??? //run { stBlock = Nil; val last = f; stBlock.foldRight(last)(Let) }

  def freshc: Code = Code(fresh)
  def reflectc(s: Op): Code = Code(reflect(s))
  def reifyc(f: => Sym) = ??? //reify { val Code(r) = f; r }
}

import Stage._

type PAbsStore = Map[String, AbsValCode]

def partialAbsEval(s: Expr, σ: PAbsStore)(using Γ: FunEnv): AbsValCode =
  s match {
    case Var(x) => σ(x)
    case Lit(i) => Interval.from(i)
    case BinOp(op, e1, e2) =>
      (partialAbsEval(e1, σ), partialAbsEval(e2, σ)) match {
        case (AbsIntV(i), Code(x)) => reflectc(Op(op, List(i, x)))
        case (Code(x), AbsIntV(i)) => reflectc(Op(op, List(x, i)))
        case (Code(x), Code(y)) => reflectc(Op(op, List(x, y)))
        case (AbsIntV(i1), AbsIntV(i2)) => absEvalOp(op, i1, i2)
      }
    case Call(fname, args) => ??? // absExecFun(Γ(fname), args.map(absEval(_, σ)))
  }

def partialAbsExec(s: Stmt, σ: PAbsStore)(using Γ: FunEnv): (Option[AbsValCode], PAbsStore) =
  s match {
    case Skip => (None, σ)
    case Assign(x, e) => ??? //(None, σ ⊔ Map(x -> absEval(e, σ)))
    case SSeq(s1, s2) => ???
      /*
      absExec(s1, σ) match {
        case (Some(v1), σ1) => (Some(v1), summon[Lattice[AbsStore]].bot) ⊔ absExec(s2, σ1)
        case (None, σ1) => absExec(s2, σ1)
      }
       */
    case Cond(e, s1, s2) =>
      val c = partialAbsEval(e, σ)
      /*
      val thn = if (Interval.from(1) ⊑ c) Some(absExec(s1, σ)) else None
      val els = if (Interval.from(0) ⊑ c) Some(absExec(s2, σ)) else None
      (thn ⊔ els).get
       */
      ???
    case While(e, s) =>
      /*
      val loop: ((Option[AbsVal], AbsStore)) => (Option[AbsVal], AbsStore) = {
        case (rt, σ) =>
          if (Interval.from(1) ⊑ absEval(e, σ)) absExec(s, σ)
          else (rt, σ)
      }
      if (!(Interval.from(1) ⊑ absEval(e, σ))) (None, σ)
      else lfp(loop)((None, σ))
       */
      ???
    case Ret(e) => (Some(partialAbsEval(e, σ)), σ)
  }
