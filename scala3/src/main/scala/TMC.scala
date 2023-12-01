package tmc

// temporal model checking via abstract interpretation

// language

abstract class Expr

abstract class AExpr extends Expr
case class EInt(n: Int) extends AExpr
case class EVar(x: String) extends AExpr
case class EBinOp(e1: AExpr, e2: AExpr) extends AExpr

abstract class BExpr extends Expr
case class TT() extends BExpr
case class FF() extends BExpr
case class Cmp(op: String, e1: AExpr, e2: Expr) extends BExpr
case class Logical(op: String, e1: BExpr, e2: BExpr) extends BExpr

type Label = Int

abstract class Stmt:
  var lab: Label = 0
  def at: Label = lab
case class Assign(x: String, e: AExpr) extends Stmt
case class Skip() extends Stmt
case class Cond(e: BExpr, thn: Stmt, els: Stmt) extends Stmt
case class While(e: BExpr, body: Stmt) extends Stmt
case class Seq(s1: Stmt, s2: Stmt) extends Stmt

// Regular spec

abstract class Regex
case class Eps() extends Regex
case class Inv(lab: Label, e: BExpr) extends Regex
case class Concat(r1: Regex, r2: Regex) extends Regex
case class Alt(r1: Regex, r2: Regex) extends Regex
case class Star(r: Regex) extends Regex
case class Plus(r: Regex) extends Regex

// Note: DNF in our Alt representation is a bit different from the paper.
// In our representation, Alt is either top level, or is the tail of an Alt.
// If neither of the alternatives is Alt, then they do not contain Alt.

def altAppend(a1: Regex, a2: Regex): Regex =
  a1 match
    case Alt(a1hd, a1tl) => Alt(a1hd, altAppend(a1tl, a2))
    case _ => Alt(a1, a2)

// concats two dnf regex, and the result is still in dnf
def dnfConcat(r1: Regex, r2: Regex): Regex =
  (r1, r2) match
    case (Alt(r1hd, r1tl), Alt(r2hd, r2tl)) =>
      Alt(Concat(r1hd, r2hd), altAppend(dnfConcat(r1hd, r2tl), dnfConcat(r1tl, r2)))
    case (r1, Alt(r2hd, r2tl)) => Alt(Concat(r1, r2hd), dnfConcat(r1, r2tl))
    case (Alt(r1hd, r1tl), r2) => Alt(Concat(r1hd, r2), dnfConcat(r1tl, r2))
    case _ => Concat(r1, r2)

def altStarize(a: Regex): Regex =
  def altStarizeAux(a: Regex): Regex =
    a match
      case Alt(hd, tl) => Concat(Star(hd), altStarizeAux(tl))
      case _ => Star(a)
  Star(altStarizeAux(a))

// convert any regular expression to its disjunctive normal form
def dnf(r: Regex): Regex = r match
  case Eps() => Eps()
  case Inv(l, e) => Inv(l, e)
  case Concat(r1, r2) => dnfConcat(dnf(r1), dnf(r2))
  case Alt(r1, r2) => Alt(dnf(r1), dnf(r2))
  case Star(r) => altStarize(dnf(r))
  case Plus(r) => dnf(Concat(r, Star(r)))

// FIXME: matchEmp is not complete
def matchEmp(r: Regex): Boolean =
  r match
    case Eps() => true
    case _ => false

// fstnxt takes non-empty Alt-free regular expressions
def fstnxt(r: Regex): (Inv, Regex) = r match
  case r@Inv(l, e) => (r, Eps())
  case Concat(r1, r2) if matchEmp(r1) => fstnxt(r2)
  case Concat(r1, r2) =>
    val (r1f, r1n) = fstnxt(r1)
    if (matchEmp(r1n)) (r1f, r2)
    else (r1f, Concat(r1n, r2))
  case Plus(r) =>
    val (rf, rn) = fstnxt(r)
    if (matchEmp(rn)) (rf, Star(rn))
    else (rf, Concat(rn, Star(rn)))
  case _ => throw new Exception("Impossible")

// Sign domain

abstract class Sign
case class Pos() extends Sign
case class Neg() extends Sign
case class Zro() extends Sign

type Value = Set[Sign]
type Env = Map[String, Value]

case class State(lab: Label, env: Env)

object TMC {
  def main(args: Array[String]): Unit = {
    // Test DNF
    val tru = TT()
    val fls = FF()
    val r1 = Alt(Inv(0, tru), Alt(Inv(1, tru), Inv(2, tru)))
    val r2 = Alt(Inv(3, tru), Alt(Inv(4, tru), Inv(5, tru)))
    assert(dnfConcat(r1, r2) ==
      Alt(Concat(Inv(0,TT()),Inv(3,TT())),
        Alt(Concat(Inv(0,TT()),Inv(4,TT())),
          Alt(Concat(Inv(0,TT()),Inv(5,TT())),
            Alt(Concat(Inv(1,TT()),Inv(3,TT())),
              Alt(Concat(Inv(1,TT()),Inv(4,TT())),
                Alt(Concat(Inv(1,TT()),Inv(5,TT())),
                  Alt(Concat(Inv(2,TT()),Inv(3,TT())),
                    Alt(Concat(Inv(2,TT()),Inv(4,TT())),
                      Concat(Inv(2,TT()),Inv(5,TT())))))))))))

    assert(altStarize(r1) ==
      Star(Concat(Star(Inv(0,TT())),Concat(Star(Inv(1,TT())),Star(Inv(2,TT()))))))
  }
}
