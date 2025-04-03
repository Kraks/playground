package zonotope

enum Act:
  case Relu()

import Act.*

enum Expr:
  case Input()
  case Nonlinear(act: Act, x: String)
  case Linear(coeffs: List[(Double, String)], const: Double)
import Expr.*

type Stmt = (String, Expr)
type NN = List[Stmt]

// concrete evaluation

type Env = Map[String, Double]

def evalAct(a: Act, x: Double): Double = a match
  case Relu() => if x < 0 then 0 else x

def evalStmt(s: Stmt, ρ: Env): Env =
  val (x, e) = s
  e match
    case Input() if ρ.contains(x) => ρ
    case Nonlinear(act, y) => ρ + (x -> evalAct(act, ρ(y)))
    case Linear(coeffs, const) =>
      val sum = coeffs.map((c, y) => c * ρ(y)).sum + const
      ρ + (x -> sum)

def evalNN(nn: NN, ρ: Env): Env =
  nn.foldLeft(ρ) { (ρ, s) => evalStmt(s, ρ) }

// abstract evaluation using zonotopes

extension (xs: List[Double])
  def ⊕(ys: List[Double]): List[Double] = xs.zip(ys).map((x, y) => x + y)

extension (x: Double)
  def *(v: Var): Var = Var(x * v.center, v.generators.map(_ * x))

case class Var(center: Double, generators: List[Double]):
  def genDim: Int = generators.size
  def +(that: Var): Var =
    assert(this.genDim == that.genDim)
    Var(center + that.center, this.generators ⊕ that.generators)
  def newGenDim(newSize: Int): Var = Var(center, generators.padTo(newSize, 0.0))
  def extendGen(extSize: Int): Var =
    assert(extSize > 0)
    Var(center, generators.padTo(genDim + extSize, 0.0))
  def ub: Double = center + generators.map((g) => if (g > 0) g else -g).sum
  def lb: Double = center + generators.map((g) => if (g > 0) -g else g).sum
  def relu: Var =
    if (lb >= 0) this
    else if (ub <= 0) Var(0, List.fill(genDim)(0.0))
    else
      val λ = ub / (ub - lb)
      val η = (ub * (1 - λ)) / 2
      (λ * this).extendGen(1) + Var(η, List.fill(genDim)(0.0) ++ List(η))

case class Zonotope(dims: Map[String, Var]):
  def contains(x: String): Boolean = dims.contains(x)
  def apply(x: String): Var = dims(x)
  def +(xv: (String, Var)): Zonotope =
    val v = xv._2
    val ρ =
      if (v.genDim < genDim)
        dims + (xv._1 -> v.newGenDim(genDim))
      else if (v.genDim > genDim)
        dims.map((k, w) => (k, w.newGenDim(v.genDim))) + xv
      else dims + xv
    Zonotope(ρ)
  def genDim: Int = dims.values.headOption.map(_.genDim).getOrElse(0)
  def dim: Int = dims.size

def absEvalAct(a: Act, x: Var): Var = a match
  case Relu() => x.relu

def absEvalStmt(s: Stmt, ρ: Zonotope): Zonotope =
  val (x, e) = s
  e match
    case Input() if ρ.contains(x) => ρ
    case Nonlinear(act, y) => ρ + (x -> absEvalAct(act, ρ(y)))
    case Linear(coeffs, const) =>
      val c: Double = coeffs.map((c, y) => c * ρ(y).center).sum + const
      val g: List[Double] = (0 until ρ.genDim).toList.map( i =>
        coeffs.map((c, y) => c * ρ(y).generators(i)).sum + const
      )
      ρ + (x -> Var(c, g))

def absEvalNN(nn: NN, ρ: Zonotope): Zonotope =
  nn.foldLeft(ρ) { (ρ, s) =>
    val a = absEvalStmt(s, ρ)
    println(a)
    a
  }

@main
def test(): Unit = {
  {
  val ex = List(
    ("x1", Input()),
    ("x2", Linear(List((0.5, "x1")), 2.0)),
    ("x3", Nonlinear(Relu(), "x2")),
  )
  val res = evalNN(ex, Map("x1" -> 10.0))
  assert(res("x3") == 7.0)
  }

  {
    val v1 = Var(0, List(1, 0))
    val v2 = Var(1, List(0, 1))
    assert(v1 + v2 == Var(1, List(1, 1)))
    val v3 = Var(3, List(1, 1))
    assert(v3.ub == 5)
    val v4 = Var(-.1, List(1))
    assert(v4.lb == -1.1)
    assert(v4.ub == 0.9)
  }

  {
    val v = Var(0, List(1))
    assert(v.lb == -1.0)
    assert(v.ub ==  1.0)
    assert(absEvalAct(Relu(), v) == Var(0.25, List(0.5, 0.25)))
  }

  {
  val ex = List(
    ("v1", Input()),
    ("v2", Linear(List((-1, "v1")), 0.0)),
    ("v3", Linear(List((1, "v1"), (1, "v2")), 0))
  )
  val res = evalNN(ex, Map("v1" -> 10.0))
  }

  {
  val e = Linear(List((3, "x"), (2, "y")), 0)
  val z = Zonotope(Map("x" -> Var(1, List(2, 3)), "y" -> Var(0, List(1, 1))))
  assert(absEvalStmt(("z", e), z)("z") == Var(3.0, List(8.0, 11.0)))
  }

  {
  val ρ = Zonotope(Map("x1" -> Var(1, List(3, 1))))
  val ex = List(
    ("x1", Input()),
    ("x2", Linear(List((-1, "x1")), 0.0)),
    ("x3", Linear(List((1, "x1"), (1, "x2")), 0.0))
  )
  assert(absEvalNN(ex, ρ)("x3") == Var(.0, List(.0, .0)))
  }

  {
  val ρ = Zonotope(Map("x1" -> Var(1, List(3, 1))))
  val ex = List(
    ("x1", Input()),
    ("x2", Linear(List((-1, "x1")), 0.0)),
    ("x3", Nonlinear(Relu(), "x2")),
    ("x4", Linear(List((1, "x2"), (2, "x3")), 5.0))
  )
  println(absEvalNN(ex, ρ)("x4"))
  }

}