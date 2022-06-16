package rewriting.re2

import rewriting._

// Better normal form representation

enum Re:
  case Chr(a: Char)
  case Seq(rs: List[Re])
  case Alt(rs: Set[Re])
  case Star(r: Re)

val emp = Re.Alt(Set())
val eps = Re.Seq(List())

def seq(rs: List[Re]): Re = {
  val rs2 = rs.flatMap { 
    case Re.Seq(rs) => rs 
    case x => List(x)
  }
  if (rs2.contains(emp)) emp
  else if (rs2.size == 1) rs2.head
  else Re.Seq(rs2)
}

def alt(rs: Set[Re]): Re = {
  val rs2 = rs.flatMap {
    case Re.Alt(rs) => rs
    case x => Set(x)
  }
  if (rs2.size == 1) rs2.head
  else Re.Alt(rs2)
}

def star(a: Re): Re = 
  a match {
    case Re.Alt(rs) if rs.isEmpty => eps 
    case Re.Seq(rs) if rs.isEmpty => eps
    case Re.Star(_) => a
    case _ => Re.Star(a)
  }

// Conversion/Normalization

def norm(r: re.Re): Re = 
  r match {
    case re.Re.Eps => eps
    case re.Re.Emp => emp
    case re.Re.Chr(c) => Re.Chr(c)
    case re.Re.Alt(a,b) => alt(Set(norm(a),norm(b)))
    case re.Re.Seq(a,b) => seq(List(norm(a),norm(b)))
    case re.Re.Star(a) => star(norm(a))
  }

// Reifies the normal form back to original syntax

def reify(r: Re): re.Re =
  r match {
    case Re.Chr(r) => re.Re.Chr(r)
    case Re.Seq(rs) => rs.map(reify).foldLeft(re.Re.Eps)(re.Re.Seq)
    case Re.Alt(rs) => rs.map(reify).foldLeft(re.Re.Eps)(re.Re.Alt)
    case Re.Star(r) => re.Re.Star(reify(r))
  }
  
@main def main(): Unit = {
  val c = Re.Chr('c')
  val d = Re.Chr('d')
  val z = alt(Set(c, d, emp, eps))
  println(alt(Set(z, z, c))) // Alt(Set(Chr(c), Chr(d), Seq(List())))
  println(seq(List(emp, c, d))) // Alt(Set())
  println(reify(z)) // Alt(Alt(Alt(Eps,Chr(c)),Chr(d)),Eps)
}