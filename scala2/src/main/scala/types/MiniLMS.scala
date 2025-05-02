package minilms

// Code in The Essence of Multi-Stage Evaluation in LMS

abstract class Exp
case class Lit(x: Int) extends Exp
case class Lit2(x: Int) extends Exp
case class Lit2N(x: Exp) extends Exp
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

abstract class Val extends Exp
case class Cst(x: Int) extends Val
case class Clo(env: List[Val], e: Exp) extends Val
case class Code(e: Exp) extends Val

object ANF {
  trait Exp
  trait V extends Exp

  case class Lam(body: Exp) extends Exp
  case class App(v1: Exp, v2: Exp) extends Exp
  case class Tic() extends Exp

  case class Let(rhs: Exp, body: Exp) extends Exp

  case class Var(x: Int) extends V
  case class Lit(x: Int) extends V

  var stFresh = 0
  var stBlock: List[Exp] = Nil
  def run[A](f: => A): A = {
    val sF = stFresh
    val sB = stBlock
    try f finally { stFresh = sF; stBlock = sB }
  }
  def fresh() = { stFresh += 1; Var(stFresh - 1) }
  def reflect(s: Exp) = { stBlock :+= s; fresh() }
  def reify(f: => Exp) = run { stBlock = Nil; val last = f; stBlock.foldRight(last) { (a, b) => Let(a, b) } }

  def anf(env: List[Exp], e: Exp): Exp = e match {
    case Lit(n) => Lit(n)
    case Var(n) => env(n)
    case Tic() => reflect(Tic())
    case Lam(e) => reflect(Lam(reify(anf(env:+fresh(), e))))
    case App(e1, e2) => reflect(App(anf(env, e1), anf(env, e2)))
    case Let(e1, e2) => anf(env:+(anf(env, e1)), e2)
  }
}

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
    case Op2(op, e1, e2) =>
      val Code(n1) = evalms(env, e1)
      val Code(n2) = evalms(env, e2)
      reflectc(Op2(op, n1, n2))
    case Var2(n) => env(n)
    case Tic2() => reflectc(Tic())
    case Lam2(e) =>
      reflectc(Lam(reifyc(evalms(env:+freshc(), e))))
    case Let2(e1, e2) => evalms(env:+evalms(env, e1), e2)
    case App2(e1, e2) =>
      val Code(s1) = evalms(env, e1)
      val Code(s2) = evalms(env, e2)
      reflectc(App(s1, s2))
  }

  // Section 7

  type Rep[T] = Exp
  def lit(n: Int): Rep[Int] = Lit(n)
  def tic() = reflect(Tic())
  def app[A,B](f: Rep[A => B],x: Rep[A]): Rep[B] = reflect(App(f,x))
  def lam[A,B](f: Rep[A]=>Rep[B]): Rep[A=>B] = reflect(Lam(reify(f(fresh()))))
  def op2(op: String, x: Rep[Int], y: Rep[Int]): Rep[Int] = reflect(Op2(op, x, y))

  def evalms2(env: List[Val], e: Exp): Val = e match {
    case Lit(n) => Cst(n)
    case Op("+", e1, e2) =>
      val Cst(n1) = evalms2(env, e1)
      val Cst(n2) = evalms2(env, e2)
      Cst(n1 + n2)
    case Var(n) => env(n)
    case Tic() => Cst(tick())
    case Lam(e) => Clo(env, e)
    case Let(e1, e2) => evalms2(env :+ evalms2(env, e1), e2)
    case App(e1, e2) =>
      val Clo(env3, e3) = evalms2(env, e1)
      evalms2(env3 :+ evalms2(env, e2), e3)

    case Clo(c_env, f) => Clo(c_env, f)
    case Code(x) => Code(x)
    case Cst(n) => Cst(n)

    case Op2(op, e1, e2) =>
      val Code(n1) = evalms2(env, e1)
      val Code(n2) = evalms2(env, e2)
      Code(op2(op, n1, n2))
    case Var2(n) => env(n)
    case Let2(e1, e2) => evalms2(env:+evalms2(env, e1), e2)
    case Lit2N(e) =>
      val Cst(n) = evalms2(env, e)
      Code(lit(n))
    case Tic2() => Code(tic())
    case Lam2(e) =>
      val f = evalms2(env, e)
      val f1 = { x:Exp => val Code(r) = evalms2(env, App(f, Code(x))); r }
      Code(lam(f1))
    case App2(e1, e2) =>
      val Code(s1) = evalms2(env, e1)
      val Code(s2) = evalms2(env, e2)
      Code(App(s1, s2))
  }

  def main(args: Array[String]): Unit = {
    //val r = evalms(Nil, Lam2(Op2("+", Lit2(21), Op2("+", Var(0), Lit2(42)))))
    val r = evalms2(Nil, App2(Lam2(Lam(Op2("+", Lit2N(Lit(21)), Op2("+", Var(0), Lit2N(Lit(42)))))),
                              Op2("*", Lit2N(Lit(100)), Lit2N(Lit(101)))))
    println(stBlock)
    println(r)
  }
}

