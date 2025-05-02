package minilms

abstract class Exp
case class Lit(x: Int) extends Exp
case class Lit2(x: Int) extends Exp
case class Op(op: String, e1: Exp, e2: Exp) extends Exp
case class Op2(op: String, e1: Exp, e2: Exp) extends Exp
case class Var(x: Int) extends Exp
case class Var2(x: Int) extends Exp
case class Tic() extends Exp
case class Tic2() extends Exp
case class Lam(e: Exp) extends Exp
case class Lam2(e: Exp) extends Exp
case class Let(e1: Exp, e2: Exp) extends Exp
case class Let2(e1: Exp, e2: Exp) extends Exp
case class App(e1: Exp, e2: Exp) extends Exp
case class App2(e1: Exp, e2: Exp) extends Exp

abstract class Val
case class Cst(x: Int) extends Val
case class Clo(env: List[Val], e: Exp) extends Val
case class Code(e: Exp) extends Val

object MiniLMS {
  var stFresh = 0
  var stBlock: List[Exp] = Nil
  def run[A](f: => A): A = {
    val sF = stFresh
    val sB = stBlock
    try f finally { stFresh = sF; stBlock = sB }
  }

  var stC = 0
  def tick() = { stC += 1; stC - 1 }

  def fresh() = { stFresh += 1; Var(stFresh-1) }
  def reflect(s: Exp) = { stBlock :+= s; fresh() }
  def reify(f: => Exp) = run { stBlock = Nil; val last = f; stBlock.foldRight(last)(Let) }
  def freshc() = Code(fresh())
  def reflectc(s: Exp) = Code(reflect(s))
  def reifyc(f: => Val) = reify { val Code(r) = f; r }

  def evalms(env: List[Val], e: Exp): Val = e match {
    case Lit(n) => Cst(n)
    case Op("+", e1, e2) =>
      val Cst(n1) = evalms(env, e1)
      val Cst(n2) = evalms(env, e2)
      Cst(n1 + n2)
    case Var(n) => env(n)
    case Tic() => Cst(tick())
    case Lam(e) => Clo(env, e)
    case Let(e1, e2) => evalms(env :+ evalms(env, e1), e2)
    case App(e1, e2) =>
      val Clo(env3, e3) = evalms(env, e1)
      evalms(env3 :+ evalms(env, e2), e3)
    case Lit2(n) => Code(Lit(n))
    case Op2("+", e1, e2) =>
      val Code(n1) = evalms(env, e1)
      val Code(n2) = evalms(env, e2)
      reflectc(Op2("+", n1, n2))
    case Var2(n) => env(n)
    case Tic2() => reflectc(Tic())
    //case Lam2(Lam(e)) =>
    case Lam2(e) =>
      reflectc(Lam(reifyc(evalms(env:+freshc(), e))))
    case Let2(e1, e2) => evalms(env:+evalms(env, e1), e2)
    case App2(e1, e2) =>
      val Code(s1) = evalms(env, e1)
      val Code(s2) = evalms(env, e2)
      reflectc(App(s1, s2))
  }

  def main(args: Array[String]): Unit = {
    val r = evalms(Nil, Lam2(Op2("+", Lit2(21), Op2("+", Var(0), Lit2(42)))))
    println(stBlock)
    println(r)
  }
}

