package continuation.shift0

enum Term:
  case Var(x: String)
  case Lam(x: String, e: Term)
  case App(e1: Term, e2: Term)
  case Reset0(e: Term)
  case Shift0(f: String, e: Term)

import Term._
