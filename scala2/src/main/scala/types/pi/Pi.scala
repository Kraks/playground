package types.pi

object PiLang {
  type Branch = (String, Exp)

  trait Exp
  case object ESet extends Exp
  case object EOne extends Exp
  case object EUnit extends Exp
  case class EVar(x: String) extends Exp
  case class ELam(pt: Pattern, e: Exp) extends Exp
  case class EPi(pt: Pattern, ty: Exp, e: Exp) extends Exp
  case class ESig(pt: Pattern, ty: Exp, e: Exp) extends Exp
  case class EPair(p1: Exp, p2: Exp) extends Exp
  case class EFst(p: Exp) extends Exp
  case class ESnd(p: Exp) extends Exp
  case class ECons(name: String, e: Exp) extends Exp
  case class ESum(cases: List[Branch]) extends Exp
  case class EFun(cases: List[Branch]) extends Exp
  case class ELet(dec: Decl, body: Exp) extends Exp
  case class EApp(e1: Exp, e2: Exp) extends Exp

  trait Decl
  case class Let(pt: Pattern, ty: Exp, e: Exp) extends Decl
  case class Letrec(pt: Pattern, ty: Exp, e: Exp) extends Decl

  trait Pattern
  case object PUnit extends Pattern
  case class PVar(x: String) extends Pattern
  case class PPair(p1: Pattern, p2: Pattern) extends Pattern

  trait Clo
  case class Closure(pt: Pattern, body: Exp, env: Env) extends Clo
  case class ClosureCompose(clo: Clo, name: String) extends Clo

  trait Value
  case object VUnit extends Value
  case object VSet extends Value
  case object VOne extends Value
  case class VLam(clo: Clo) extends Value
  case class VFun(choices: List[Branch], env: Env) extends Value
  case class VPair(v1: Value, v2: Value) extends Value
  case class VCons(name: String, v: Value) extends Value
  case class VPi(tv: Value, clo: Clo) extends Value
  case class VSig(tv: Value, clo: Clo) extends Value
  case class VSum(choices: List[Branch], env: Env) extends Value
  case class VNeutral(n: Neut) extends Value

  type Env = List[(Pattern, Either[Value, Decl])]

  trait Neut

  def error(msg: String) = throw new RuntimeException(msg)

  def fst(v: Value): Value = ???
  def snd(v: Value): Value = ???

  def inPattern(x: String, p: Pattern): Boolean = p match {
    case PUnit => false
    case PVar(y) => x == y
    case PPair(p1, p2) => inPattern(x, p1) || inPattern(x, p2)
  }

  def projPattern(p: Pattern, x: String, v: Value): Value = p match {
    case PVar(y) if x == y => v
    case PPair(p1, p2) if inPattern(x, p1) => projPattern(p1, x, fst(v))
    case PPair(p1, p2) if inPattern(x, p2) => projPattern(p1, x, snd(v))
    case _ => error("cannot project pattern")
  }

  def eval(e: Exp, env: Env): Value = ???

  def lookup(env: Env, x: String): Value = env match {
    case Nil => error("empty environment")
    case (pt, Left(v))::env if (inPattern(x, pt)) => projPattern(pt, x, v) 
    case (pt, Right(Let(_, ty, e)))::env if (inPattern(x, pt)) => projPattern(pt, x, eval(e, env)) 
    case env0@((pt, Right(Letrec(_, ty, e)))::env) if (inPattern(x, pt)) => projPattern(pt, x, eval(e, env0)) 
    case _::env => lookup(env, x)
  }

  
}

