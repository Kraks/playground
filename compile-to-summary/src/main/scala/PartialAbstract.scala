package compositional

// Author: Guannan Wei <guannanwei@purdue.edu>
// A ``multi-stage'' abstract interpreter that can generate code
// for analyzing currently unknown functions.

import Expr._
import Stmt._
import Stage._

type AbsValCode = Interval | Sym

type PAbsStore = Map[String, AbsValCode]

object AbsValCodeInstance {
  given AbsValCodeLattice: Lattice[AbsValCode] with
    val lit = summon[Lattice[Interval]]
    def bot: AbsValCode = lit.bot
    def top: AbsValCode = lit.top
    extension (l1: AbsValCode)
      // Idea: we need some modality over lattice ⟨S, ⊑⟩
      def ⊑(l2: AbsValCode): Boolean =
        (l1, l2) match {
          case (i1: Interval, i2: Interval) =>
            given lit: Lattice[Interval] = IntervalLattice; import lit._
            i1 ⊑ i2
          case (_, i) if i == top => true
          case (i, _) if i == bot => false
          case (x, y) if x == y => true
          //case (_, x: Sym) => true // Note: we actually don't know since x is next stage
          case (_, _) => ??? // Note: next stage boolean?
        }
      def ⊔(l2: AbsValCode): AbsValCode =
        (l1, l2) match {
          case (i1: Interval, i2: Interval) =>
            given lit: Lattice[Interval] = IntervalLattice; import lit._
            i1 ⊔ i2
          case (i: Interval, x: Sym) =>
            if (i == bot) x
            else if (i == top) i
            else reflectc(Op("⊔", List(i, x)))
          case (x: Sym, i: Interval) =>
            if (i == bot) x
            else if (i == top) i
            else reflectc(Op("⊔", List(x, i)))
          case (x: Sym, y: Sym) =>
            if (x == y) x
            else reflectc(Op("⊔", List(x, y)))
        }
      def ⊓(l2: AbsValCode): AbsValCode =
        (l1, l2) match {
          case (i1: Interval, i2: Interval) =>
            given lit: Lattice[Interval] = IntervalLattice; import lit._
            i1 ⊓ i2
          case (i: Interval, x: Sym) => reflectc(Op("⊓", List(i, x)))
          case (x: Sym, i: Interval) => reflectc(Op("⊓", List(x, i)))
          case (x: Sym, y: Sym) => reflectc(Op("⊓", List(x, y)))
        }
}

import AbsValCodeInstance.given
import scala.collection.immutable.HashMap

def partialAbsEval(s: Expr, σ: PAbsStore | Sym)(using Γ: FunEnv): AbsValCode =
  s match {
    case Var(x) => σ match {
      case (σ: Map[String, AbsValCode]) => σ(x)
      case (σ: Sym) => reflectc(Op("store-apply", List(σ, x)))
    }
    case Lit(i) => Interval.from(i)
    case BinOp(op, e1, e2) =>
      (partialAbsEval(e1, σ), partialAbsEval(e2, σ)) match {
        case (i1: Interval, i2: Interval) => absEvalOp(op, i1, i2)
        case (i: Interval, x: Sym) => reflectc(Op(op, List(i, x)))
        case (x: Sym, i: Interval) => reflectc(Op(op, List(x, i)))
        case (x: Sym, y: Sym) => reflectc(Op(op, List(x, y)))
      }
    case Call(fname, args) => ??? // absExecFun(Γ(fname), args.map(absEval(_, σ)))
  }

def isStatic(v: Option[AbsValCode]): Boolean =
  v match {
    case Some(i: Interval) => true
    case None => true
    case _ => false
  }
def isStatic(σ: PAbsStore): Boolean =
  σ.foldLeft(true) { case (b, (k, v)) => b && v.isInstanceOf[Interval] }

type T = (Option[AbsValCode]|Sym, PAbsStore|Sym)
def partialLfp(f: T => T)(t: T): T =
  t match {
    case (t1: Option[AbsValCode], t2: PAbsStore) if isStatic(t1) && isStatic(t2) =>
      // all static
      f(t) match {
        case (r: Option[AbsValCode], s: PAbsStore) if isStatic(r) && isStatic(s) =>
          // return is all static too
          if ((r, s) ⊑ (t1, t2)) t
          else {
            given ins: AbsDomain[(Option[AbsVal], AbsStore)] = ProductAbsDomain
            import ins._
            val next = (r.asInstanceOf[Option[AbsVal]], s.asInstanceOf[AbsStore]) ▽ (t1.asInstanceOf[Option[AbsVal]], t2.asInstanceOf[AbsStore])
            partialLfp(f)(next)
          }
        case _ =>
          // return is partially static or all dynamic
          // residualize is safe; but it seems we can still do something more here in some cases
          (unit(t._1), unit(t._2))
      }
    case t =>
      // partially static or all dynamic
      (unit(t._1), unit(t._2))
  }

// XXX: return Option[AbsValCode]?
def partialAbsExec(s: Stmt, σ: PAbsStore | Sym)(using Γ: FunEnv): (Option[AbsValCode] | Sym, PAbsStore | Sym) =
  s match {
    case Skip => (None, σ)
    case Assign(x, e) =>
      //println(s); println(σ)
      σ match {
        case (σ: Map[String, AbsValCode]) =>
          //println("store" + s)
          (None, σ ⊔ Map(x -> partialAbsEval(e, σ)))
        case (σ: Sym) =>
          //println("sym")
          val res = reflectc(Op("⊔", List(σ, Map(x -> partialAbsEval(e, σ)))))
          (None, res)
      }
    case SSeq(s1, s2) =>
      partialAbsExec(s1, σ) match {
        case (Some(v1), σ1) => partialAbsExec(s2, σ1) match {
          case (v2: Option[AbsValCode], σ2) => (Some(v1) ⊔ v2, σ2)
          case (v2: Sym, σ2) => (Some(v1 ⊔ v2), σ2)
        }
        case (None, σ1) => partialAbsExec(s2, σ1)
        case (x: Sym, σ1) => partialAbsExec(s2, σ1) match {
          case (Some(v2), σ2) => ((x ⊔ v2).asInstanceOf[Sym], σ2)
          case (None, σ2) => (x, σ2)
          case (v2: Sym, σ2) => ((x ⊔ v2).asInstanceOf[Sym], σ2)
        }
      }
    case Cond(e, s1, s2) =>
      partialAbsEval(e, σ) match {
        case (c: Interval) =>
          val (thn_v, thn_σ) = if (Interval.from(1) ⊑ c) partialAbsExec(s1, σ) else (None, Map())
          val (els_v, els_σ) = if (Interval.from(0) ⊑ c) partialAbsExec(s2, σ) else (None, Map())
          val v: Option[AbsValCode]|Sym = (thn_v, els_v) match {
            case (v1: Option[AbsValCode], v2: Option[AbsValCode]) => v1 ⊔ v2
            case (Some(v), x: Sym)  => Some(v ⊔ x)
            case (None, x: Sym) => x
            case (x: Sym, Some(v)) => Some(x ⊔ v)
            case (x: Sym, None) => x
          }
          val s: PAbsStore|Sym = (thn_σ, els_σ) match {
            case (s1: PAbsStore, s2: PAbsStore) => s1 ⊔ s2
            case (s1: PAbsStore, x: Sym) => reflectc(Op("⊔", List(s1, x)))
            case (x: Sym, s2: PAbsStore) => reflectc(Op("⊔", List(x, s2)))
            case (x: Sym, y: Sym) => reflectc(Op("⊔", List(x, y)))
          }
          (v, s)
        case (x: Sym) =>
          val thnCnd = reflectc(Op("⊑", List(Interval.from(1), x)))
          val elsCnd = reflectc(Op("⊑", List(Interval.from(0), x)))
          val thnBlock = reify0 { partialAbsExec(s1, σ) }
          val elsBlock = reify0 { partialAbsExec(s2, σ) }
          val res_s = reflectc(Op("if-⊔", List(thnCnd, thnBlock, elsCnd, elsBlock)))
          val res = reflectc(Op("get-res", List(res_s)))
          val s = reflectc(Op("get-store", List(res_s)))
          (res, s)
      }
    case While(e, s) =>
      val loop: (T) => T = { case (rt, σ) =>
        partialAbsEval(e, σ) match {
          case (c: Interval) =>
            if (Interval.from(1) ⊑ c) partialAbsExec(s, σ)
            else (rt, σ)
          case (c: Sym) =>
            // Note: binop = should be interpreted abstractly in the interval domain
            val cnd = reifyExpr { partialAbsEval(e, _) }
            val body = reify1 { partialAbsExec(s, _) }
            val ret_s = reflectc(Op("while-lfp", List(cnd, body, σ)))
            val ret = reflectc(Op("get-res", List(ret_s)))
            val st = reflectc(Op("get-store", List(ret_s)))
            (ret, st)
        }
      }
      partialLfp(loop)((None, σ)) match {
        case (ret: Sym, st: Sym) =>
          // Here is some duplication, as we did not distinguish dynamic result from
          // dynamic condition (where no iteration is performed) or dynamic body (where partial iterations have performed)
          val cnd = reifyExpr { partialAbsEval(e, _) }
          val body = reify1 { partialAbsExec(s, _) }
          val ret_s_* = reflectc(Op("while-lfp", List(cnd, body, ret, st)))
          val ret_* = reflectc(Op("get-res", List(ret_s_*)))
          val st_* = reflectc(Op("get-store", List(ret_s_*)))
          (ret_*, st_*)
        case result => result
      }
    case Ret(e) => (Some(partialAbsEval(e, σ)), σ)
  }

def partialAbsExecFun(fdef: FunDef, vs: List[AbsValCode])(using Γ: FunEnv): AbsValCode =
  val FunDef(_, params, body) = fdef
  val (Some(ret), σ) = partialAbsExec(body, params.zip(vs).toMap)
  ret

def partialAbsRun(p: Program, entrance: String, args: AbsValCode*): AbsValCode =
  given funEnv: FunEnv = p.funEnv
  partialAbsExecFun(funEnv(entrance), args.toList)

@main def main() = {
  val lit = summon[Lattice[Interval]]
  def bot: AbsValCode = lit.bot
  def top: AbsValCode = lit.top
}
