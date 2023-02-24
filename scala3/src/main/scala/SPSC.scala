package supercompilation.spsc

// An re-implementation of SPSC in Scala 3

// SPSC: a Simple Supercompiler in Scala
// by Ilya Kyyuchnikov and Sergei Romanenko

enum TKind:
  case Ctr
  case FCall
  case GCall

import TKind._

abstract class Term
case class Var(name: String) extends Term
case class CFG(kind: TKind, name: String, args: List[Term]) extends Term {
  def withArgs(newArgs: List[Term]): CFG = CFG(kind, name, newArgs)
}
case class Let(term: Term, bindings: List[(Var, Term)]) extends Term
case class Pat(name: String, args: List[Var]) extends Term

class CFGObject(kind: TKind) extends ((String, List[Term]) => CFG) {
  def apply(name: String, args: List[Term]) = CFG(kind, name, args)
  def unapply(e: CFG) = if (e.kind == kind) Some(e.name, e.args) else None
}
object CFGCtr extends CFGObject(Ctr)
object CFGFCall extends CFGObject(FCall)
object CFGGCall extends CFGObject(GCall)

abstract class Def {
  def name: String
}
case class FFun(name: String, args: List[Var], term: Term) extends Def
case class GFun(name: String, p: Pat, args: List[Var], term: Term) extends Def

case class Program(defs: List[Def]) {
  val f: Map[String, FFun] = defs.foldLeft[Map[String, FFun]](Map()) {
    case (m, x: FFun) => m + (x.name -> x)
    case (m, _) => m
  }
  val g: Map[(String, String), GFun] = defs.foldLeft[Map[(String, String), GFun]](Map()) {
    case (m, x: GFun) => m + ((x.name, x.p.name) -> x)
    case (m, _) => m
  }
  val gs: Map[String, List[GFun]] = defs.foldLeft[Map[String, List[GFun]]](Map().withDefaultValue(Nil)) {
    case (m, x: GFun) => m + (x.name -> (x :: m(x.name)))
    case (m, _) => m
  }
}

object Algebra {
  def subst(t: Term, m: Map[Var, Term]): Term = t match {
    case v: Var => m.getOrElse(v, v)
    case e: CFG => e.withArgs(e.args.map(subst(_, m)))
  }

  def equiv(t1: Term, t2: Term): Boolean = inst(t1, t2) && inst(t2, t1)

  def inst(t1: Term, t2: Term): Boolean = findSubst(t1, t2) != null

  def shallowEq(e1: CFG, e2: CFG): Boolean = e1.kind == e2.kind && e1.name == e2.name

  def findSubst(t1: Term, t2: Term): Map[Var, Term] = {
    val m = collection.mutable.Map[Var, Term]()
    def walk(t1: Term, t2: Term): Boolean = (t1, t2) match {
      case (v1: Var, _) =>
        val x = m.getOrElse(v1, t2)
        m.update(v1, t2)
        val y = m(v1) // XXX: is it the right thing? the original code use Scala 2.8 API
        x == y
      case (e1: CFG, e2: CFG) if shallowEq(e1, e2) =>
        e1.args.zip(e2.args).forall(walk)
      case _ => false
    }
    if (walk(t1, t2)) m.toMap.filter { case (k, v) => k != v }
    else null
  }

  def vars(t: Term): List[Var] = t match {
    case v: Var => List(v)
    case e: CFG => e.args.foldLeft(List[Var]()) { _ ++ vars(_) }
  }

  def trivial(t: Term): Boolean = t match {
    case CFGFCall(_, _) | CFGGCall(_, _) => false
    case _ => true
  }
}
