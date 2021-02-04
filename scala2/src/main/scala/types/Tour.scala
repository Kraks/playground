package types.tour

// CS502 - Guannan Wei

object Basic {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr

  trait Value
  case class FunV(f: Value ⇒ Value) extends Value

  type Env = Map[String, Value]

  def interp(e: Expr, ρ: Env): Value = e match {
    case Var(x) ⇒ ρ(x)
    case Lam(x, body) ⇒ FunV(v ⇒ interp(body, ρ + (x → v)))
    case App(e1, e2) ⇒ interp(e1, ρ) match {
      case FunV(f) ⇒ f(interp(e2, ρ))
    }
  }
}

object BasicDefunc {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr

  trait Value
  case class FunV(λ: Lam, ρ: Env) extends Value

  type Env = Map[String, Value]

  def interp(e: Expr, ρ: Env): Value = e match {
    case Var(x) ⇒ ρ(x)
    case Lam(x, body) ⇒ FunV(Lam(x, body), ρ)
    case App(e1, e2) ⇒ interp(e1, ρ) match {
      case FunV(Lam(x, body), ρ_*) ⇒
        interp(body, ρ_* + (x → interp(e2, ρ)))
    }
  }
}

object BasicWithData {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr
  case class Lit(i: Int) extends Expr
  case class Aop(op: String, e1: Expr, e2: Expr) extends Expr
  case class Let(x: String, e: Expr, body: Expr) extends Expr

  trait Value
  case class FunV(f: Value ⇒ Value) extends Value
  case class IntV(x: Int) extends Value

  type Env = Map[String, Value]

  def interp(e: Expr, ρ: Env): Value = e match {
    case Var(x) ⇒ ρ(x)
    case Lam(x, body) ⇒ FunV(v ⇒ interp(body, ρ + (x → v)))
    case App(e1, e2) ⇒ interp(e1, ρ) match {
      case FunV(f) ⇒ f(interp(e2, ρ))
    }
    case Lit(i) ⇒ IntV(i)
    case Aop("+", e1, e2) ⇒
      val IntV(v1) = interp(e1, ρ)
      val IntV(v2) = interp(e2, ρ)
      IntV(v1 + v2)
    case Let(x, e, body) ⇒
      val v = interp(e, ρ)
      interp(body, ρ + (x → v))
  }
}

object BasicWithDataAndState {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr
  case class Lit(i: Int) extends Expr
  case class Aop(op: String, e1: Expr, e2: Expr) extends Expr
  case class Seq(e1: Expr, e2: Expr) extends Expr
  case class Assign(x: String, e: Expr) extends Expr
  case class Let(x: String, e: Expr, body: Expr) extends Expr
  case class If0(cnd: Expr, thn: Expr, els: Expr) extends Expr
  case class Letrec(x: String, e: Expr, body: Expr) extends Expr

  type Addr = Int
  type Env = Map[String, Addr]
  type Heap = Map[Addr, Value]
  type Result = (Value, Heap)

  def alloc(σ: Heap): Addr = σ.size + 1

  trait Value
  case class FunV(f: (Value, Heap) ⇒ (Value, Heap)) extends Value
  case class IntV(x: Int) extends Value
  case class BotV() extends Value

  def interp(e: Expr, ρ: Env, σ: Heap): Result = e match {
    case Var(x) ⇒ (σ(ρ(x)), σ)
    case Lam(x, body) ⇒ (FunV({ case (v, σ) ⇒
                                val α = alloc(σ)
                                interp(body, ρ + (x → α), σ + (α → v))
                              }), σ)
    case App(e1, e2) ⇒
      val (FunV(f), σ_*) = interp(e1, ρ, σ)
      val (v, σ_**) = interp(e2, ρ, σ_*)
      f(v, σ_**)
    case Lit(i) ⇒ (IntV(i), σ)
    case Aop("+", e1, e2) ⇒
      val (IntV(v1), σ_*) = interp(e1, ρ, σ)
      val (IntV(v2), σ_**) = interp(e2, ρ, σ_*)
      (IntV(v1 + v2), σ_**)
    case Aop("*", e1, e2) ⇒
      val (IntV(v1), σ_*) = interp(e1, ρ, σ)
      val (IntV(v2), σ_**) = interp(e2, ρ, σ_*)
      (IntV(v1 * v2), σ_**)
    case Aop("-", e1, e2) ⇒
      val (IntV(v1), σ_*) = interp(e1, ρ, σ)
      val (IntV(v2), σ_**) = interp(e2, ρ, σ_*)
      (IntV(v1 - v2), σ_**)
    case Seq(e1, e2) ⇒
      val (_, σ_*) = interp(e1, ρ, σ)
      interp(e2, ρ, σ_*)
    case Assign(x, e) ⇒
      val (v, σ_*) = interp(e, ρ, σ)
      (v, σ_* + (ρ(x) → v))
    case Let(x, e, body) ⇒
      val (v, σ_*) = interp(e, ρ, σ)
      val α = alloc(σ_*)
      val ρ_* = ρ + (x → α)
      val σ_** = σ_* + (α → v)
      interp(body, ρ_*, σ_**)
    case If0(cnd, thn, els) ⇒ interp(cnd, ρ, σ) match {
      case (IntV(0), σ_*) ⇒ interp(thn, ρ, σ_*)
      case (IntV(_), σ_*) ⇒ interp(els, ρ, σ_*)
    }
    case Letrec(x, e, body) ⇒
      val α = alloc(σ)
      val ρ_* = ρ + (x → α)
      val σ_* = σ + (α → BotV())
      val (v, σ_**) = interp(e, ρ_*, σ_*)
      val σ_*** = σ_** + (α → v)
      interp(body, ρ_*, σ_***)
  }

  def main(args: Array[String]) = {
    val fact = Letrec("fact",
      Lam("x",
        If0(Var("x"), Lit(1),
          Aop("*", Var("x"), App(Var("fact"), Aop("-", Var("x"), Lit(1)))))),
      App(Var("fact"), Lit(5)))
    println(interp(fact, Map(), Map()))

    val nonterm = Letrec("x",
      Aop("+", Var("x"), Lit(1)),
      Var("x"))
    //println(interp(nonterm, Map(), Map()))
  }
}

object CPSInterp {
  trait Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr
  case class Lit(i: Int) extends Expr
  case class Aop(op: String, e1: Expr, e2: Expr) extends Expr
  case class Seq(e1: Expr, e2: Expr) extends Expr
  case class Assign(x: String, e: Expr) extends Expr
  case class Let(x: String, e: Expr, body: Expr) extends Expr
  case class If0(cnd: Expr, thn: Expr, els: Expr) extends Expr
  case class Letrec(x: String, e: Expr, body: Expr) extends Expr
  case class Letcc(x: String, body: Expr) extends Expr

  type Addr = Int
  type Env = Map[String, Addr]
  type Heap = Map[Addr, Value]
  type Result = (Value, Heap)
  type Cont = (Value, Heap) ⇒ (Value, Heap)

  def alloc(σ: Heap): Addr = σ.size + 1

  trait Value
  case class FunV(f: (Value, Heap, Cont) ⇒ (Value, Heap)) extends Value
  case class IntV(x: Int) extends Value
  case class BotV() extends Value
  case class ContV(k: Cont) extends Value

  def interp(e: Expr, ρ: Env, σ: Heap)(k: Cont): Result = e match {
    case Var(x) ⇒ k(σ(ρ(x)), σ)
    case Lam(x, body) ⇒ k(FunV({
      case (v, σ, k_*) ⇒
        val α = alloc(σ)
        interp(body, ρ + (x → α), σ + (α → v))(k_*)
    }), σ)
    case App(e1, e2) ⇒ interp(e1, ρ, σ) {
      case (FunV(f), σ_*) ⇒ interp(e2, ρ, σ_*) {
        case (v, σ_**) ⇒ f(v, σ_**, k)
      }
      case (ContV(k), σ_*) ⇒ interp(e2, ρ, σ_*)(k)
    }
    case Lit(i) ⇒ k(IntV(i), σ)
    case Aop("+", e1, e2) ⇒ interp(e1, ρ, σ) {
      case (IntV(v1), σ_*) ⇒ interp(e2, ρ, σ_*) {
        case (IntV(v2), σ_**) ⇒ k(IntV(v1 + v2), σ_**)
      }
    }
    case Aop("*", e1, e2) ⇒ interp(e1, ρ, σ) {
      case (IntV(v1), σ_*) ⇒ interp(e2, ρ, σ_*) {
        case (IntV(v2), σ_**) ⇒ k(IntV(v1 * v2), σ_**)
      }
    }
    case Aop("-", e1, e2) ⇒ interp(e1, ρ, σ) {
      case (IntV(v1), σ_*) ⇒ interp(e2, ρ, σ_*) {
        case (IntV(v2), σ_**) ⇒ k(IntV(v1 - v2), σ_**)
      }
    }
    case Seq(e1, e2) ⇒ interp(e1, ρ, σ) {
      case (_, σ_*) ⇒ interp(e2, ρ, σ_*)(k)
    }
    case Assign(x, e) ⇒ interp(e, ρ, σ) {
      case (v, σ_*) ⇒ k(v, σ_* + (ρ(x) → v))
    }
    case Let(x, e, body) ⇒ interp(e, ρ, σ) {
      case (v, σ_*) ⇒
        val α = alloc(σ_*)
        val ρ_* = ρ + (x → α)
        val σ_** = σ_* + (α → v)
        interp(body, ρ_*, σ_**)(k)
    }
    case If0(cnd, thn, els) ⇒ interp(cnd, ρ, σ) {
      case (IntV(0), σ_*) ⇒ interp(thn, ρ, σ_*)(k)
      case (IntV(_), σ_*) ⇒ interp(els, ρ, σ_*)(k)
    }
    case Letrec(x, e, body) ⇒
      val α = alloc(σ)
      val ρ_* = ρ + (x → α)
      val σ_* = σ + (α → BotV())
      interp(e, ρ_*, σ_*) {
        case (v, σ_**) ⇒
          val σ_*** = σ_** + (α → v)
          interp(body, ρ_*, σ_***)(k)
      }
    case Letcc(x, e) ⇒
      val α = alloc(σ)
      val ρ_* = ρ + (x → α)
      val σ_* = σ + (α → ContV(k))
      interp(e, ρ_*, σ_*)(k)
  }

  def main(args: Array[String]) = {
    val fact = Letrec("fact",
      Lam("x",
        If0(Var("x"), Lit(1),
          Aop("*", Var("x"), App(Var("fact"), Aop("-", Var("x"), Lit(1)))))),
      App(Var("fact"), Lit(5)))
    println(interp(fact, Map(), Map()){ case (v, σ) => (v, σ) })

    // letcc k in
    // 1 + k(2)
    val e = Letcc("k", Aop("+", Lit(1), App(Var("k"), Lit(2))))
    println(interp(e, Map(), Map()){ case (v, σ) => (v, σ) })

    // letcc k in
    // let a = ? in
    // let b = if0 a then k(0) else 1 + 2
    // let c = b + 1
    // c
    val e2 = Letcc("k",
                  Let("a", Lit(2),
                      Let("b", If0(Var("a"), App(Var("k"), Lit(0)), Aop("+", Lit(1), Lit(2))),
                          Let("c", Aop("+", Var("b"), Lit(1)),
                              Var("c")))))

    println(interp(e2, Map(), Map()){ case (v, σ) => (v, σ) })
  }
}

object CPS2Interp {
  trait Expr
  case class Lit(i: Int) extends Expr
  case class Var(x: String) extends Expr
  case class Lam(x: String, body: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr
  case class Aop(op: String, e1: Expr, e2: Expr) extends Expr
  case class Letcc(k: String, e: Expr) extends Expr
  case class Reset(e: Expr) extends Expr
  case class Shift(k: String, e: Expr) extends Expr

  trait Value
  case class IntV(i: Int) extends Value
  case class FunV(λ: Lam, ρ: Env) extends Value
  case class ContV(k: Cont ⇒ Cont) extends Value

  type Env = Map[String, Value]
  type MCont = Value ⇒ Value
  type Cont = (Value, MCont) ⇒ Value

  def interp(e: Expr, ρ: Env)(k: Cont)(r: MCont): Value = e match {
    case Lit(i) ⇒ k(IntV(i), r)
    case Var(x) ⇒ k(ρ(x), r)
    case Lam(x, body) ⇒ k(FunV(Lam(x, body), ρ), r)
    case Aop("+", e1, e2) ⇒
      interp(e1, ρ)({
        case (IntV(i1), r) ⇒ interp(e2, ρ)({
          case (IntV(i2), r) ⇒ k(IntV(i1+i2), r)
        })(r)
      })(r)
    case App(e1, e2) ⇒
      interp(e1, ρ)({
        case (FunV(Lam(x, body), ρ_*), r) ⇒
          interp(e2, ρ)({
            case (v, r) ⇒ interp(body, ρ_* + (x → v))(k)(r)
          })(r)
        case (ContV(k_*), r) ⇒ interp(e2, ρ)(k_*(k))(r)
      })(r)
    case Letcc(x, e) ⇒
      val ρ_* = ρ + (x → ContV((k_*) ⇒ { case (v, r) ⇒ k(v, r) }))
      interp(e, ρ_*)(k)(r)
    case Reset(e) ⇒
      interp(e, ρ)({ case (v, r) => r(v) })(v => k(v, r))
    case Shift(x, e) ⇒
      val ρ_* = ρ + (x → ContV((k_*) ⇒ { case (v, r) ⇒ k(v, z ⇒ k_*(z, r)) }))
      interp(e, ρ_*)({ case (v, r) ⇒ r(v) })(r)
  }

  def run(e: Expr): Value = interp(e, Map())({ case (v, r) ⇒ r(v) })(x ⇒ x)

  def main(args: Array[String]) = {
    val e1 = Aop("+", Lit(1),
      Letcc("k1", Aop("+", Lit(2), Aop("+", Lit(3),
        Letcc("k2", Aop("+", Lit(4),
          App(Var("k1"), Lit(5))))))))
    assert(run(e1) == IntV(6))

    val e2 = Aop("+", Lit(1),
      Letcc("k1", Aop("+", Lit(2), Aop("+", Lit(3),
        Letcc("k2", Aop("+", Lit(4),
          App(Var("k2"), Lit(5))))))))
    assert(run(e2) == IntV(11))

    val e3 = Aop("+", Lit(5),
      Reset(Aop("+", Lit(2),
        Shift("k", Aop("+", Lit(1), App(Var("k"), App(Var("k"), Lit(3))))))))
    assert(run(e3) == IntV(13))

    val e4 = Aop("+", Lit(5),
      Reset(Aop("+", Lit(3),
        Shift("k", Aop("+", App(Var("k"), Lit(0)), App(Var("k"), Lit(1)))))))
    assert(run(e4) == IntV(12))
  }
}

object PartialEval {
  trait Value
  case class IntV(i: Int) extends Value

  case class FunDef(args: List[String], body: Expr)
  val placeHolder = FunDef(List(), Lit(0))

  trait Expr
  case class Lit(i: Int) extends Expr {
    override def toString = i.toString
  }
  case class Var(x: String) extends Expr
  case class App(e1: String, es: List[Expr]) extends Expr
  case class Aop(op: String, e1: Expr, e2: Expr) extends Expr
  case class If0(cnd: Expr, thn: Expr, els: Expr) extends Expr

  type FEnv = Map[String, FunDef]
  type Env = Map[String, Value]

  def interp(e: Expr, fs: FEnv, ρ: Env): Value = e match {
    case Lit(i) ⇒ IntV(i)
    case Var(x) ⇒ ρ(x)
    case Aop("+", e1, e2) ⇒
      val IntV(v1) = interp(e1, fs, ρ)
      val IntV(v2) = interp(e2, fs, ρ)
      IntV(v1 + v2)
    case Aop("-", e1, e2) ⇒
      val IntV(v1) = interp(e1, fs, ρ)
      val IntV(v2) = interp(e2, fs, ρ)
      IntV(v1 - v2)
    case Aop("*", e1, e2) ⇒
      val IntV(v1) = interp(e1, fs, ρ)
      val IntV(v2) = interp(e2, fs, ρ)
      IntV(v1 * v2)
    case If0(cnd, thn, els) ⇒ interp(cnd, fs, ρ) match {
      case IntV(0) ⇒ interp(thn, fs, ρ)
      case IntV(_) ⇒ interp(els, fs, ρ)
    }
    case App(f, es) ⇒
      val FunDef(args, body) = fs(f)
      val vs = es.map(e ⇒ interp(e, fs, ρ))
      val ρ_* = args.zip(vs).foldLeft(ρ) { _ + _ }
      interp(body, fs, ρ_*)
  }

  def peval(e: Expr, fs: FEnv, ρ: Env): (FEnv, Expr) = e match {
    case Lit(i) ⇒ (fs, e)
    case Var(x) ⇒ ρ.get(x) match {
      case Some(IntV(i)) ⇒ (fs, Lit(i))
      case None ⇒ (fs, e)
    }
    case Aop("+", e1, e2) ⇒
      val (fs1, e1_*) = peval(e1, fs, ρ)
      val (fs2, e2_*) = peval(e2, fs1, ρ)
      (e1_*, e2_*) match {
        case (Lit(i1), Lit(i2)) ⇒ (fs2, Lit(i1+i2))
        case (_, _) ⇒ (fs2, Aop("+", e1_*, e2_*))
      }
    case Aop("-", e1, e2) ⇒
      val (fs1, e1_*) = peval(e1, fs, ρ)
      val (fs2, e2_*) = peval(e2, fs1, ρ)
      (e1_*, e2_*) match {
        case (Lit(i1), Lit(i2)) ⇒ (fs2, Lit(i1-i2))
        case (_, _) ⇒ (fs2, Aop("-", e1_*, e2_*))
      }
    case Aop("*", e1, e2) ⇒
      val (fs1, e1_*) = peval(e1, fs, ρ)
      val (fs2, e2_*) = peval(e2, fs1, ρ)
      (e1_*, e2_*) match {
        case (Lit(i1), Lit(i2)) ⇒ (fs2, Lit(i1*i2))
        case (_, _) ⇒ (fs2, Aop("*", e1_*, e2_*))
      }
    case If0(cnd, thn, els) ⇒ peval(cnd, fs, ρ) match {
      case (fs_cnd, Lit(i)) ⇒
        if (i == 0) peval(thn, fs_cnd, ρ)
        else peval(els, fs_cnd, ρ)
      case (fs_cnd, cnd_*) ⇒
        val (fs_thn, thn_*) = peval(thn, fs_cnd, ρ)
        val (fs_els, els_*) = peval(els, fs_thn, ρ)
        (fs_els, If0(cnd_*, thn_*, els_*))
    }
    case App(f, es) ⇒
      val FunDef(args, body) = fs(f)
      val (fs_*, vs) = es.foldLeft((fs, List[Expr]())) {
        case ((fs, vs), e) =>
          val (fs_e, v) = peval(e, fs, ρ)
          (fs_e, vs ++ List(v))
      }
      val argsAndVals = args.zip(vs)
      val (statics, dynamics) = argsAndVals.partition { case (a, v) ⇒ v.isInstanceOf[Lit] }
      val ρ_* = statics.map({case (a, Lit(i)) ⇒ (a, IntV(i))}).toMap
      if (dynamics.isEmpty) {
        peval(body, fs_*, ρ_*)
      } else {
        val new_f = f + "_" + statics.map(_._2).mkString("_")
        if (!fs_*.contains(new_f)) {
          val (fs_body, body_*) = peval(body, fs_* + (new_f → placeHolder), ρ_*)
          val new_fs = fs_body + (new_f → FunDef(dynamics.map(_._1), body_*))
          (new_fs, App(new_f, dynamics.map(_._2)))
        } else {
          (fs_*, App(new_f, dynamics.map(_._2)))
        }
      }
  }

  def main(args: Array[String]) = {
    def fundefs =
      Map(("power" → FunDef(List("x", "n"),
             If0(Var("n"),
                 Lit(1),
                 Aop("*", Var("x"), App("power", List(Var("x"), Aop("-", Var("n"), Lit(1)))))))))
    def e1 = App("power", List(Lit(2), Lit(4)))

    println(interp(e1, fundefs, Map()))

    def e2 = App("power", List(Var("a"), Lit(4)))
    println(peval(e2, fundefs, Map()))

    def e3 = App("power", List(Lit(2), Var("n")))
    println(peval(e3, fundefs, Map()))
  }
}
