package mk

// Classic microKanren

object Mk {
  trait Term
  case class Var(x: Int) extends Term {
    override def toString = "#" + x.toString
  }

  case class Pair(x: Var, y: Term) extends Term {
    override def toString = s"${x.toString} → ${y.toString}"
  }

  case class Data(d: Any) extends Term {
    override def toString = d.toString
  }

  case class State(st: Subst, ct: Int)
  val mtState = State(List(), 0)

  trait Stream
  object MtStm extends Stream                            // empty stream
  case class MStm(st: State, stm: Stream) extends Stream // mature stream
  case class ImmStm(f: () => Stream) extends Stream      // immature stream

  type Subst = List[Pair]
  type Goal = State ⇒ Stream

  def walk(u: Term, s: Subst): Term = u match {
    case Var(uv) =>
      val pr = s.find((p) => p.x == u)
      if (pr.nonEmpty) walk(pr.get.x, s) else u
    case _ => u
  }

  def ext(x: Var, v: Term, s: Subst): Subst = Pair(x, v)::s

  val mzero: Stream = MtStm
  def unit(st: State): Stream = MStm(st, MtStm)

  def ===(u: Term, v: Term): Goal = { sc =>
    unify(u, v, sc.st) match {
      case Some(st) => unit(State(st, sc.ct))
      case None => mzero
    }
  }

  def unify(u: Term, v: Term, s: Subst): Option[Subst] = {
    (walk(u, s), walk(v, s)) match {
      case (u, v) if u == v => Some(s)
      case (Var(x), v) => Some(ext(Var(x), v, s))
      case (u, Var(y)) => Some(ext(Var(y), u, s))
      case (u@Pair(_,_), v@Pair(_,_)) =>
        for (s1 <- unify(u.x, v.x, s); s2 <- unify(u.y, v.y, s1)) yield s2
      case (_, _) => None
    }
  }

  def callFresh(f: Var => Goal): Goal = { sc =>
    f(Var(sc.ct))(State(sc.st, sc.ct+1))
  }

  def disj(g1: Goal, g2: Goal): Goal = { sc => mplus(g1(sc), g2(sc)) }
  def conj(g1: Goal, g2: Goal): Goal = { sc => bind(g1(sc), g2) }

  /* Depth-first search */
  def mplus_dfs(s1: Stream, s2: Stream): Stream = s1 match {
    case MtStm => s2
    case MStm(s, s1tl) => MStm(s, mplus_dfs(s1tl, s2))
    case ImmStm(f) => ImmStm(() => mplus_dfs(f(), s2))
  }

  /* Interleaving streams */
  def mplus(s1: Stream, s2: Stream): Stream = s1 match {
    case MtStm => s2
    case MStm(s, s1tl) => MStm(s, mplus(s1tl, s2))
    case ImmStm(f) => ImmStm(() => mplus(s2, f()))
  }

  def bind(s: Stream, g: Goal): Stream = s match {
    case MtStm => mzero
    case MStm(s, stl) => mplus(g(s), bind(stl, g))
    case ImmStm(f) => ImmStm(() => bind(f(), g))
  }
}

object HelloMk extends App {
  println("Hello microKanren in Scala.")
  import Mk._

  def five(x: Term): Goal = disj(===(x, Data(5)),
                                 (sc) => ImmStm(() => five(x)(sc)))
  println(callFresh(five)(mtState))

  def sixes(x: Term): Goal = disj(===(x, Data(6)),
                                  (sc) => ImmStm(() => sixes(x)(sc)))
  def fiveAndSixes: Goal = callFresh((x) => disj(sixes(x), sixes(x)))
  println(fiveAndSixes(mtState))
}

