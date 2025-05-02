package rewriting.hereditary

// De Bruijn indices

enum Db:
  case Var(x: Int)
  case Lam(l: Db)
  case App(a: Db, b: Db)

def liftR(f: Int => Int): Int => Int =
  (n) => if (n == 0) 0 else f(n-1) + 1

// rename all variable `i` to `f(i)` in `a`
def rename(a: Db, f: Int => Int): Db =
  a match {
    case Db.Var(n) => Db.Var(f(n))
    case Db.Lam(l) => Db.Lam(rename(l, liftR(f)))
    case Db.App(a, b) => Db.App(rename(a, f), rename(b, f))
  }

def shift(e: Db, f: Int => Db): Int => Db =
  (n) => if (n == 0) e else f(n-1)

def liftS(f: Int => Db): Int => Db =
  shift(Db.Var(0), k => rename(f(k), (_+1)))

// parallel substitution
def subst(e: Db, f: Int => Db): Db =
  e match {
    case Db.Var(n) => f(n)
    case Db.Lam(l) => Db.Lam(subst(l, liftS(f)))
    case Db.App(a, b) => app(subst(a, f), subst(b, f))
  }

// Only substitutes the first variable 0 -> v in e
// Decrement all other variable indices
def subst0(e: Db, v: Db): Db =
  subst(e, (n) => if (n == 0) v else Db.Var(n-1))

// Or:
// def subst0(e: Db, b: Db): Db = subst(e, shift(v, Db.Var))

def app(a: Db, b: Db): Db =
  a match {
    case Db.Lam(e) => subst0(e, b)
    case _ => Db.App(a, b)
  }

def norm(a: Db): Db =
  a match {
    case Db.Var(n) => Db.Var(n)
    case Db.Lam(l) => Db.Lam(norm(l))
    case Db.App(a, b) => app(norm(a), norm(b))
  }

@main def main(): Unit = {
  import Db._
  // (\x.x) (\x.x)
  val t = App(Lam(Var(0)), Lam(Var(0)))
  println(s"$t -> ${norm(t)}")

  // (\f.\x.f(x)) (\x.x)
  val t1 = App(Lam(Lam(App(Var(1), Var(0)))), Lam(Var(0)))
  println(s"$t1 -> ${norm(t1)}")

  println(rename(Lam(Var(0)), n => n + 1))
  println(rename(Lam(Var(1)), n => n + 1))
}