package scalogno

import scala.collection._

/*

trait Base {
  val Backtrack = new Exception
  var varCount: Int = 0
  def freshId: Int = {
    val id = varCount
    varCount += 1
    id
  }

  implicit class RelOps(a: => Rel) {
    def &&(b: => Rel) = infix_&&(a,b)
    def ||(b: => Rel) = infix_||(a,b)
  }
  implicit class ExpOps[T](a: Exp[T]) {
    def ===[U](b: Exp[U]) = infix_===(a,b)
  }

  def exists[T,U](f: (Exp[T],Exp[U]) => Rel): Rel = {
    f(fresh[T],fresh[U])
  }
  def exists[T,U,V](f: (Exp[T],Exp[U],Exp[V]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V])
  }
  def exists[T,U,V,W](f: (Exp[T],Exp[U],Exp[V],Exp[W]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W])
  }
  def exists[T,U,V,W,X](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X])
  }
  def exists[T,U,V,W,X,Y](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X],Exp[Y]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X],fresh[Y])
  }
  def exists[T,U,V,W,X,Y,Z](f: (Exp[T],Exp[U],Exp[V],Exp[W],Exp[X],Exp[Y],Exp[Z]) => Rel): Rel = {
    f(fresh[T],fresh[U],fresh[V],fresh[W],fresh[X],fresh[Y],fresh[Z])
  }

  // Dynamically scoped variables

  var dvars: Map[Int, Any] = Map[Int, Any]()
  case class DVar[T](id: Int, default: T) extends (() => T) {
    dvarSet(id, default)
    def apply: T = dvarGet[T](id)
    def :=(v: T) = dvarSet[T](id, v)
  }
  var dvarCount = 1
  def DVar[T](v: T): DVar[T] = {
    val id = dvarCount
    dvarCount += 1
    DVar[T](id, v)
  }
  def dvarSet[T](id: Int, v: T): Unit = dvars += (id -> v)
  def dvarGet[T](id: Int): T = dvar(id).asInstanceOf[T]
  def dvarUpd[T](id: Int)(f: T => T): Unit = dvarSet(id, fdvarGet(id))

  // Goals and relations

  trait Rel { def exec(call: Exec)(k: Cont): Unit }
  type Exec = GoalThunk => Cont => Unit
  type Cont = () => Unit
  type GoalThunk = () => Rel

  // Unconditional success
  val Yes = new Rel { def exec(call: Exec)(k: Cont) = k() }

  // Unconditional failure
  val No = new Rel { def exec(call: Exec)(k: Cont) = throw Backtrack }

  def infix_&&(a: => Rel, b: => Rel): Rel =
    new Rel {
      def exec(call: Exec)(k: Cont) = call(() => a) { () => call(() => b)(k) }
    }

  def infix_||(a: => Rel, b: => Rel): Rel =
    new Rel {
      def exec(call: Exec)(k: Cont) = { call(() => a)(k); call(() => b)(k) }
    }

  // Logic terms
  case class Exp[+T](id: Int)
  def fresh[T] = Exp(freshId)

  def exists[T](f: Exp[T] => Rel): Rel = f(fresh)
  def infix_===[T](a: => Exp[T], b: => Exp[T]): Rel = {
    register(IsEqual(a, b))
    Yes
  }
  def term[T](key: String, args: List[Exp[Any]]): Exp[T] = {
    val e = fresh[T]
    register(IsTerm(e.id, key, args))
    e
  }

  // Constraints
  abstract class Constraint
  case class IsTerm(id: Int, key: String, args: List[Exp[Any]]) extends Constraint
  case class IsEqual(x: Exp[Any], y: Exp[Any]) extends Constraint
  // TODO: NotEqual?

  var cstore: Set[Constraint] = Set[Constraint]()
  def conflict(cs: Set[Constraint], c: Constraint): Boolean = {
    def prop(c1: Constraint, c2: Constraint)(fail: () => Nothing): List[Constraint] =
      (c1, c2) match {
        case (IsEqual(a1, b1), IsEqual(a2, b2)) if a1 == a2 || a1 == b2 || b1 == a2 || b1 == b2 =>
          List(IsEqual(a1, a2), IsEqual(a1, b2), IsEqual(b1, a2), IsEqual(b1, b2))
        case (IsEqual(Exp(a), Exp(b)), IsTerm(a1, key, args)) if a == a1 =>
          List(IsTerm(b, key, args))
        case (IsEqual(Exp(a), Exp(b)), IsTerm(b1, key, args)) if b == b1 =>
          List(IsTerm(a, key, args))
        case (IsTerm(a1, key, args), IsEqual(Exp(a), Exp(b))) if a == a1 =>
          List(IsTerm(b, key, args))
        case (IsTerm(b1, key, args), IsEqual(Exp(a), Exp(b))) if b == b1 =>
          List(IsTerm(a, key, args))
        case (IsTerm(a1, key1, args1), IsTerm(a2, key2, args2)) if a1 == a2 =>
          if (key1 != key2 || args1.length != args2.length) fail()
            (args1, args2).zipped.map(IsEqual(_, _))
        case _ => Nil
      }
    val cn = for { c2 <- cs } yield prop(c, c2)(() => throw Backtrack)
    cstore += c
    cn.foreach(register)
    false
  }

  def register(c: Constraint): Unit = {
    if (cstore.contains(c)) return
    // GW: conflict can only return false?
    if (conflict(cstore, c)) throw Backtrack
  }
}

trait Engine extends Base {
  def run[T](f: Exp[T] => Rel): Seq[String] = {
    def call(e: () => Rel)(k: Cont): Unit = {
      val cstore1 = cstore
      val dvars1 = dvars
      try {
        e().exec(call)(k)
      } catch {
        case Backtrack =>
      } finally {
        cstore = cstore1
        dvars = dvars
      }
    }
    val q = fresh[T]
    val res = mutable.ListBuffer[String]()
    call(() => f(q)) { () =>
      res += extractStr(q)
    }
    res.toList
  }
}

trait Prettify {}

*/
