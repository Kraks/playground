package compositional

// Author: Guannan Wei <guannanwei@purdue.edu>
// Basic code representation/generation

case class Sym(x: Int) {
  override def toString = s"x$x"
}
case class Op(rand: String, rators: List[Any]) {
  override def toString = s"$rand(${rators.mkString(",")})"
}
case class Let(x: String, e: Op) {
  override def toString = s"let $x = $e"
}

case class Block(body: List[Let], args: List[Sym], res: Option[AbsValCode]|Sym, σ: PAbsStore|Sym) {
  override def toString = s"(${args.mkString(",")}){ ${body.mkString(",")}; ($res, $σ) }"
}

object Stage {
  var stFresh = 0
  var stBlock: List[Let] = Nil

  def session[A](f: => A): (String, A) = {
    stFresh = 0
    stBlock = Nil
    val r = f
    //println("code: \n" + stBlock.mkString("\n"))
    //println("result: " + r)
    (stBlock.mkString("\n"), r)
  }

  def run[A](f: => A): A = {
    val sF = stFresh
    val sB = stBlock
    try f finally { stBlock = sB }
  }

  def fresh: Sym = { stFresh += 1; Sym(stFresh-1) }
  def reflect(s: Op): Sym =
    val Sym(x) = fresh
    stBlock :+= Let("x"+x, s)
    Sym(x)
  def reify0(f: => (Option[AbsValCode]|Sym, PAbsStore|Sym)): Block = run {
    stBlock = Nil
    val (res, σ) = f
    Block(stBlock, List(), res, σ)
  }
  def reify1(f: Sym => (Option[AbsValCode]|Sym, PAbsStore|Sym)): Block = run {
    stBlock = Nil
    val x = fresh
    val (res, σ) = f(x)
    Block(stBlock, List(x), res, σ)
  }
  def reifyExpr(f: Sym => AbsValCode): Block = run {
    stBlock = Nil
    val x = fresh
    val res = f(x)
    Block(stBlock, List(x), Some(res), x)
  }

  def reflectc(s: Op): Sym = reflect(s)
  def unit[T](t: T): Sym = reflect(Op("id", List(t)))
}
