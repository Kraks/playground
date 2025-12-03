package anf

// Auxiliary counter for generating fresh variable names

object Counter {
  var x: Int = 0
  def fresh(prefix: String = "x"): String = {
    val n = x
    x += 1
    s"$prefix$n"
  }
  def reset: Unit = x = 0
}
import Counter.*

// Defining the source language

enum Src:
  case Num(i: Int)
  case Var(x: String)
  case Lam(x: String, e: Src)
  case App(e1: Src, e2: Src)
  case BinOp(op: String, e1: Src, e2: Src)
  case If(cnd: Src, thn: Src, els: Src)
  case Let(x: String, e1: Src, e2: Src)

// Defining the target language

enum TgtVal:
  case Num(i: Int)
  case Var(x: String)
  case Lam(x: String, e: Tgt)

enum TgtComp:
  case BinOp(op: String, v1: TgtVal, v2: TgtVal)
  case App(e1: TgtVal, e2: TgtVal)
  case If(cnd: TgtVal, thn: Tgt, els: Tgt)

// Note: strictly speaking, e1 cannot be a TgtLet in ANF, here we
// allow it for demonstrating the translation for If.
case class TgtLet(x: String, e1: Tgt, e2: Tgt)

type Tgt = TgtVal | TgtComp | TgtLet

def normalizeName(e: Src, k: TgtVal => Tgt): Tgt =
  normalize(e, t =>
    t match
      case v: TgtVal => k(v)
      case _ =>
        val x = Counter.fresh("x")
        TgtLet(x, t, k(TgtVal.Var(x)))
  )

def normalize(e: Src, k: Tgt => Tgt): Tgt = e match
  case Src.Num(i) =>
    k(TgtVal.Num(i))
  case Src.Var(x) =>
    k(TgtVal.Var(x))
  case Src.Lam(x, body) =>
    k(TgtVal.Lam(x, anf(body)))
  case Src.App(e1, e2) =>
    normalizeName(e1, v1 =>
      normalizeName(e2, v2 =>
        k(TgtComp.App(v1, v2))))
  case Src.BinOp(op, e1, e2) =>
    normalizeName(e1, v1 =>
      normalizeName(e2, v2 =>
        k(TgtComp.BinOp(op, v1, v2))))
  case Src.If(cnd, thn, els) =>
    normalizeName(cnd, v1 => k(TgtComp.If(v1, anf(thn), anf(els))))
  case Src.Let(x, e1, e2) =>
    normalize(e1, t1 =>
      TgtLet(x, t1, normalize(e2, k)))

def anf(e: Src): Tgt =
  Counter.reset
  normalize(e, t => t)

@main def test(): Unit =
  // ((λx.x+1) (2 * 3)) * (4 + 5)
  val ex1 =
    Src.BinOp("*",
      Src.App(Src.Lam("x", Src.BinOp("+", Src.Var("x"), Src.Num(1))), Src.BinOp("*", Src.Num(2), Src.Num(3))),
      Src.BinOp("+", Src.Num(4), Src.Num(5)))

  val anfEx1 = anf(ex1)
  println(anfEx1)
  /*
  let x0 = 2 * 3
  let x1 = (λx. x + 1) x0
  let x2 = 4 + 5
  x1 * x2
  */

  /* fib function in Src:
    if (n <= 1) then n
    else fib(n-1) + fib(n-2)
  */
  val ex2 =
    Src.If(
      Src.BinOp("<=", Src.Var("n"), Src.Num(1)),
      Src.Var("n"),
      Src.BinOp("+",
        Src.App(Src.Var("fib"), Src.BinOp("-", Src.Var("n"), Src.Num(1))),
        Src.App(Src.Var("fib"), Src.BinOp("-", Src.Var("n"), Src.Num(2)))
      )
    )
  val anfEx2 = anf(ex2)
  println(anfEx2)
  /*
  let x0 = n <= 1
  if x0 then n
  else
    let x0 = n - 1
    let x1 = fib(x0)
    let x2 = n - 2
    let x3 = fib(x2)
    x1 + x3
  */

  val ex3 =
    Src.Let("y", Src.If(Src.BinOp("==", Src.Num(3), Src.Num(4)), Src.BinOp("+", Src.Num(-1), Src.App(Src.Var("f"), Src.Num(10))), Src.Num(20)),
      Src.BinOp("*", Src.Var("y"), Src.Num(2))
    )
  println(anf(ex3))
