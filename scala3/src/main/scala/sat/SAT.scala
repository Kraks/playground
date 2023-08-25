package sat

import math._
import scala.util.Random

type Lit = Int
type Asn = List[Lit]
type Env = Map[Int, Boolean]

extension (asn: Asn)
  def toEnv: Env = asn.map(x => (abs(x), x > 0)).toMap
  def lookup(x: Lit): Option[Boolean] =
    for (y <- asn) {
        if (x == abs(y)) return Some(y > 0)
    }
    None

extension (env: Env)
  def toAsn: Asn = env.toList.map { case (k, v) => if (v) k else -k }

case class Clause(xs: List[Lit]) {
  override def toString = s"(${xs.mkString(" ∨ ")})"
  def size = xs.size
  def contains(v: Lit): Boolean = xs.contains(v)
  def remove(v: Lit): Clause = Clause(xs.filter(_ != v))
  def containsAnyOf(vs: List[Lit]): Boolean = {
    for (v <- vs) { if (xs.contains(v)) return true }
    return false
  }
  def ++(c: Clause): Clause = Clause((xs ++ c.xs).toSet.toList)
  def removeAllOccur(vs: List[Lit]): Clause = Clause(xs.filter(!vs.contains(_)))

  def isTrivial: Boolean = {
    val (pos, neg) = xs.partition(_ > 0)
    for (p <- pos) {
      if (neg.contains(-p)) return true
    }
    return false
  }

  def eval(ρ: Env): Boolean =
    xs.foldLeft(false) { (z, x) =>
      z || (x > 0 && ρ(abs(x))) || (x < 0 && !ρ(abs(x)))
    }

  // Returns None if evals to True
  // Returns Some(Clause(List())) if evals to False
  // Returns Some(c) for some residual clause c
  def peval(ρ: Env): Option[Clause] = {
    xs.foldLeft[Option[Clause]](Some(Clause(List()))) { (z, x) =>
      if (ρ.contains(abs(x))) {
        if ((x > 0 && ρ(abs(x))) || (x < 0 && !ρ(abs(x)))) None else z
      } else for {c <- z} yield Clause(x :: c.xs)
    }
  }

  def peval0(a: Asn): Option[Clause] = {
    xs.foldLeft[Option[Clause]](Some(Clause(List()))) { (z, x) =>
      a.lookup(abs(x)) match {
        case None => for {c <- z} yield Clause(x :: c.xs)
        case Some(b) =>
          if ((x > 0 && b) || (x < 0 && !b)) None else z
      }
    }
  }
}

case class Formula(cs: List[Clause]) {
  override def toString = s"(${cs.mkString(" ∧ ")}"

  lazy val nClauses = cs.size
  lazy val nVars = allLits.groupBy(abs).size

  lazy val allLits = cs.flatMap(_.xs).toSet
  lazy val unitVars = cs.filter(_.size == 1).map(_.xs.head).toList
  lazy val pureVars = allLits.groupBy(abs).filter(_._2.size==1).values.flatten.toList

  def resolve(l: Lit): Formula = {
    val (pos, notpos) = cs.partition(_.contains(l))
    val (neg, other) = notpos.partition(_.contains(-l))
    val poscls = pos.map(_.remove(l)).toSet
    val negcls = neg.map(_.remove(-l)).toSet
    val res = for { c1 <- poscls; c2 <- negcls } yield c1 ++ c2
    Formula((other ++ res).filter(!_.isTrivial))
  }

  def resoluionBlowup(l: Lit): Int = {
    val m = cs.filter(_.contains(l)).size
    val n = cs.filter(_.contains(-l)).size
    m * n - m - n
  }

  def posNegCount(l: Lit): Int =
    cs.filter(x => x.contains(l) || x.contains(-l)).size

  def pickFirst: Lit = cs.head.xs.head
  def pickRandom: Lit = Random.shuffle(cs.head.xs).head
  def pickMinRes: Lit = allLits.minBy(resoluionBlowup)
  def pickMostFreq: Lit = allLits.maxBy(posNegCount)

  def addClause(c: Clause): Formula = Formula(c::cs)
  def addUnit(x: Int): Formula = Formula(Clause(List(x))::cs)

  def isEmpty: Boolean = cs.isEmpty
  def hasUnsatClause: Boolean = cs.contains(Clause(List()))
  def hasUnitClause: Boolean = unitVars.size != 0

  def elimSingleUnit: (Formula, Asn) = {
    val v = unitVars.head
    //val result = for (c <- cs if !c.contains(v)) yield c.remove(-v)
    //(Formula(result), List(v))
    val asn = Map(abs(v) → (if (v > 0) true else false))
    peval(asn) match {
      case None => (Formula(List(Clause(List()))), List(v))
      case Some(f) => (f, List(v))
    }
  }

  def elimUnit: (Formula, Asn) = {
    for (u <- unitVars) {
      if (unitVars.contains(-u)) return (Formula(List(Clause(List()))), List[Lit]())
    }
    val result = for { c <- cs if !c.containsAnyOf(unitVars) }
    yield c.removeAllOccur(unitVars.map(-_))
    (Formula(result), unitVars)
  }

  def hasPureClause: Boolean = pureVars.size != 0
  def elimPure: (Formula, Asn) = (Formula(cs.filter(!_.containsAnyOf(pureVars))), pureVars)

  def eval(ρ: Env): Boolean = cs.foldLeft(true) { (z, c) => z && c.eval(ρ) }

  // Returns None if evals to False
  // Returns Some(Formula(List())) if evals to True
  // Returns Some(f) for some residual  fomula f
  def peval(ρ: Env): Option[Formula] =
    cs.foldLeft[Option[Formula]](Some(Formula(List()))) { (z, c) =>
      c.peval(ρ) match {
        case None => z
        case Some(Clause(Nil)) => None
        case Some(c) => for { f <- z } yield Formula(c :: f.cs)
      }
    }

  // Returns Formula(List(Clause(List()))) if evals to False
  // Returns Formula(List()) if evals to True
  // Returns f for some residual  fomula f
  def peval0(ρ: Asn): Formula =
    cs.foldLeft[Formula](Formula(List())) { (f, c) =>
      c.peval0(ρ) match {
        case None => f
        case Some(c) => Formula(c :: f.cs)
      }
    }
}

// DP = Unit prop + Pure var elim + Resolution
def dp(f: Formula, ρ: Asn): Option[Asn] = {
  //println(s"${f.nClauses}, ${f.nVars}")
  if (f.isEmpty) return Some(ρ)
  if (f.hasUnsatClause) return None
  if (f.hasUnitClause) {
    val (g, ρ_*) = f.elimUnit
    return dp(g, ρ_* ++ ρ)
  }
  if (f.hasPureClause) {
    val (g, ρ_*) = f.elimPure
    return dp(g, ρ_* ++ ρ)
  }
  val x = f.pickMinRes
  dp(f.resolve(x), ρ)
}

// DPLL = Unit prop + Pure var elim + Backtracking
def dpll(f: Formula, assgn: Asn): Option[Asn] = {
  if (f.hasUnsatClause) return None
  if (f.isEmpty) return Some(assgn)
  if (f.hasUnitClause) {
    val (new_f, new_assgn) = f.elimUnit
    return dpll(new_f, assgn ++ new_assgn)
  }
  if (f.hasPureClause) {
    val (new_f, new_assgn) = f.elimPure
    return dpll(new_f, assgn ++ new_assgn)
  }
  val v = f.pickMostFreq
  //val v = f.pickFirst
  val tryTrue = dpll(f.addUnit(v), assgn)
  if (tryTrue.nonEmpty) tryTrue
  else dpll(f.addUnit(-v), assgn)
}

// Iterative DPLL using an explicit trail of decisions

abstract class Decision {
  val lit: Lit
}
// Assumed as one half of a case-split
case class Guessed(lit: Lit) extends Decision
// deduced by unit propagation from literals assumed earlier
case class Deduced(lit: Lit) extends Decision
type Trail = List[Decision]

def unassigned(f: Formula, trail: Trail): Set[Lit] = {
  val s1 = f.allLits.map(abs(_)).toSet
  val s2 = trail.map(x => abs(x.lit)).toSet
  s1 diff s2
}

// f is the naked representation of a list of clause
def unitPropagateAux(f: List[List[Int]], asn: Set[Int], trail: Trail): (List[List[Int]], Set[Int], Trail) = {
  val f1: List[List[Int]] = f.map { c => c.filter(x => !asn(-x)) }
  val newUnits = f1.foldLeft(Set[Int]()) { case (acc, cls) =>
    if (cls.size == 1 && !asn(cls.head)) acc + cls.head else acc
  }
  if (newUnits.isEmpty) (f1, asn, trail)
  else {
    val trail1 = newUnits.toList.map(Deduced(_)) ++ trail
    val asn1 = newUnits ++ asn
    unitPropagateAux(f1, asn1, trail1)
  }
}

def unitPropagate(f: Formula, trail: Trail): (Formula, Trail) = {
  val fn = trail.map(_.lit).toSet
  val (f1, _, trail1) = unitPropagateAux(f.cs.map(_.xs), fn, trail)
  (Formula(f1.map(Clause(_))), trail1)
}

def backtrack(trail: Trail): Trail =
  trail match {
    case Deduced(_)::ts => backtrack(ts)
    case _ => trail
  }

def dpli(f: Formula, trail: Trail): Option[Asn] = {
  val (f1, trail1) = unitPropagate(f, trail)
  if (f1.hasUnsatClause) 
    backtrack(trail) match {
      case Guessed(p)::ts => dpli(f, Deduced(-p)::ts)
      case _ => None
    }
  else {
    val vs = unassigned(f, trail1)
    if (vs.isEmpty) Some(trail1.map(_.lit).toList)
    else {
      val p = vs.maxBy(l => f.posNegCount(l))
      dpli(f, Guessed(p)::trail1)
    }
  }
}

// TODO:
// DPLP = Unit prop + Pure var elim + _Simple_ conflict analysis + Backjumping
