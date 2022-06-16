package rewriting.re

// https://julesjacobs.com/notes/smartconstr/smartconstr.pdf
// Bottom up rewriting with smart constructors

enum Re:
  case Emp
  case Eps
  case Chr(c: Char)
  case Seq(a: Re, b: Re)
  case Alt(a: Re, b: Re)
  case Star(a: Re)

def seq(a: Re, b: Re): Re =
  (a, b) match {
    case (Re.Emp, _) => Re.Emp
    case (_, Re.Emp) => Re.Emp
    case (Re.Eps, x) => x
    case (x, Re.Eps) => x
    case (Re.Seq(x, y), b) => seq(x, seq(y, b))
    case _ => Re.Seq(a, b)
  }

def alt(a: Re, b: Re): Re =
  (a, b) match {
    case (Re.Emp, x) => x
    case (x, Re.Emp) => x
    case (Re.Alt(x, y), b) => alt(x, alt(y, b))
    case _ => if (a == b) a else Re.Alt(a, b)
  }

def star(a: Re): Re =
  a match {
    case Re.Emp => Re.Eps
    case Re.Eps => Re.Eps
    case Re.Star(_) => a
    case _ => Re.Star(a)
  }

// convert a regular expression to normal form

def norm(a: Re): Re =
  a match {
    case Re.Emp => Re.Emp
    case Re.Eps => Re.Eps
    case Re.Chr(c) => Re.Chr(c)
    case Re.Alt(a, b) => alt(norm(a), norm(b))
    case Re.Seq(a, b) => seq(norm(a), norm(b))
    case Re.Star(a) => star(norm(a))
  }

@main def main(): Unit = {
  val r = Re.Alt(Re.Star(Re.Star(Re.Seq(Re.Chr('a'),Re.Star(Re.Emp)))),Re.Emp)
  println(norm(r)) // Star(Chr('a'))
}