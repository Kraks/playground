package rewriting.nbe

// HOAS

enum Hs:
  case Lam(f: Hs => Hs)
  case App(a: Hs, b: Hs)

def app(a: Hs, b: Hs): Hs =
  a match {
    case Hs.Lam(f) => f(b)
    case _ => Hs.App(a, b)
  }

@main def main(): Unit = {
  import Hs._
  // \x.\y.app(y, \z.app(x, z))
  val t = Lam(x => Lam(y => App(y, Lam(z => App(x, z)))))

}
