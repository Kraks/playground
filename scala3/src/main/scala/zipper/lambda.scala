package zipper.lambda

// Non-Deterministic Abstract Machines
// Malgorzata Biernacka, Dariusz Biernacki, Sergueï Lenglet, Alan Schmitt

enum Ann:
  case AApp, ALam
import Ann.*

extension (a: Ann)
  def ∉(b: Set[Ann]): Boolean = !b.contains(a)

trait AnnExpr:
  val ann: Set[Ann]

enum Expr extends AnnExpr:
  case Var(name: String, ann: Set[Ann] = Set())
  case Lam(x: String, body: Expr, ann: Set[Ann] = Set())
  case App(fun: Expr, arg: Expr, ann: Set[Ann] = Set())
  override def toString: String = this match
    case Var(x, _) => x
    case Lam(x, t, _) => s"λ$x.${t.toString}"
    case App(t, s, _) => s"(${t.toString} ${s.toString})"
import Expr.*

extension (e: Expr)
  def withAnn(a: Ann): Expr = e match
    case Var(x, ann) => Var(x, ann + a)
    case Lam(x, t, ann) => Lam(x, t, ann + a)
    case App(t, s, ann) => App(t, s, ann + a)
  def subst(x: String, s: Expr): Expr = e match
    case Var(y, ann) if x == y => s
    case Var(y, ann) => Var(y, ann)
    // Assuming all variable bindings are unique
    case Lam(y, t, ann) if x != y => Lam(y, t.subst(x, s), ann)
    case App(t, u, ann) => App(t.subst(x, s), u.subst(x, s), ann)
  def erase: Expr = e match
    case Var(x, _) => Var(x, Set())
    case Lam(x, t, _) => Lam(x, t.erase, Set())
    case App(t, s, _) => App(t.erase, s.erase, Set())

enum Frame:
  case FLam(x: String)
  case FArg(t: Expr)
  case FFun(t: Expr)
import Frame.*

type Context = List[Frame]

def plugin(c: Context, t: Expr): Expr =
  c match
    case Nil => t
    case FLam(x)::rest => plugin(rest, Lam(x, t))
    case FArg(a)::rest => plugin(rest, App(t, a))
    case FFun(f)::rest => plugin(rest, App(f, t))

enum Rule:
  case appL, appR, appBeta, appLam
import Rule.*

type Stack = List[(Rule, Set[Ann])]

enum State:
  case SInit(e: Expr)
  case SNorm(e: Expr)
  // forward configuration:
  case SFApp(e: Expr, s: Stack, c: Context)
  case SFLam(e: Expr, s: Stack, arg: Expr, c: Context)
  // backward configuration:
  case SBApp(s: Stack, e: Expr, c: Context)
  case SBLam(s: Stack, e: Expr, arg: Expr, c: Context)
import State.*

def inject(e: Expr): State =
  SFApp(e, List(), List())

def step(e: State): State =
  e match
    case SInit(e) => SFApp(e, List(), List())
    case SFApp(App(t, s, ann), π, κ) if AApp ∉ t.ann =>
      SFApp(t, (appL, ann)::π, FArg(s)::κ)
    case SFApp(App(t, s, ann), π, κ) if AApp ∉ s.ann =>
      SFApp(s, (appR, ann)::π, FFun(t)::κ)
    case SFApp(App(t, s, ann), π, κ) if ALam ∉ t.ann =>
      SFLam(t, (appBeta, ann)::π, s, κ)
    case SFApp(Lam(x, t, ann), π, κ) if AApp ∉ t.ann =>
      SFApp(t, (appLam, ann)::π, FLam(x)::κ)
    case SFApp(t, π, κ) =>
      SBApp(π, t.withAnn(AApp), κ)
    case SBApp(List(), t, List()) =>
      SNorm(t)
    case SBApp((appL, ann)::π, t, FArg(s)::κ) =>
      SFApp(App(t, s, ann), π, κ)
    case SBApp((appR, ann)::π, s, FFun(t)::κ) =>
      SFApp(App(t, s, ann), π, κ)
    case SBLam((appBeta, ann)::π, t, s, κ) =>
      SFApp(App(t, s, ann), π, κ)
    case SBApp((appLam, ann)::π, t, FLam(x)::κ) =>
      SFApp(Lam(x, t, ann), π, κ)
    case SFLam(Lam(x, t, ann), π, s, κ) =>
      SInit(plugin(κ, t).subst(x, s).erase)
    case SFLam(t, π, s, κ) =>
      SBLam(π, t.withAnn(ALam), s, κ)

def run(e: Expr): Expr =
  def loop(e: State): Expr =
    e match
      case SNorm(t) => t
      case _ => loop(step(e))
  loop(inject(e)).erase

val id1 = Lam("x", Var("x"))
val id2 = Lam("y", Var("y"))

val e1 = App(id1, id2)
val e2 = App(Lam("z", Var("z")), e1)
val e3 = App(e1, Lam("z", Var("z")))
val e4 = App(e1, App(Lam("z", Var("z")), Lam("w", Var("w"))))

@main
def test(): Unit = {
  println(s"$e1 -> ${run(e1)}")
  println(s"$e2 -> ${run(e2)}")
  println(s"$e3 -> ${run(e3)}")
  println(s"$e4 -> ${run(e4)}")
}