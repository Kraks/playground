package compositional

// Author: Guannan Wei <guannanwei@purdue.edu>
// The Interval abstract domain

case class Interval private (lb: Double, ub: Double) {
  def toConst: Option[Int] = if (lb == ub) Some(lb.toInt) else None
}

object Interval {
  def make(lb: Double, ub: Double): Interval = {
    if (ub < lb) Interval(Double.PositiveInfinity, Double.NegativeInfinity)
    else Interval(lb, ub)
  }
  def from(is: Int*): Interval = Interval(is.min.toDouble, is.max.toDouble)
}

given IntIntervalGC: GaloisConn[Set[Int], Interval] with
  extension (a: Set[Int])
    def α: Interval = Interval.from(a.toSeq:_*)
  extension (b: Interval)
    def γ: Set[Int] = (b.lb.toInt to b.ub.toInt).toSet

given IntervalLattice(using ldb: Lattice[Double]): Lattice[Interval] with
  def bot = Interval.make(ldb.top, ldb.bot)
  def top = Interval.make(ldb.bot, ldb.top)
  extension (l1: Interval)
    def ⊑(l2: Interval) = l2.lb ⊑ l1.lb && l1.ub ⊑ l2.ub
    def ⊔(l2: Interval) = Interval.make(l1.lb ⊓ l2.lb, l1.ub ⊔ l2.ub)
    def ⊓(l2: Interval) = Interval.make(l1.lb ⊔ l2.lb, l1.ub ⊓ l2.ub)

given IntervalAbsDomain(using lit: Lattice[Interval]): AbsDomain[Interval] with
  extension (l1: Interval)
    def ▽(l2: Interval): Interval =
      Interval.make(if (l1.lb ⊑ l2.lb) l1.lb else Double.NegativeInfinity,
                    if (l2.ub ⊑ l1.ub) l1.ub else Double.PositiveInfinity)
    def △(l2: Interval): Interval =
      Interval.make(if (l1.lb == Double.NegativeInfinity) l2.lb else l1.lb,
                    if (l1.ub == Double.PositiveInfinity) l2.ub else l1.ub)

given IntervalArith: Arith[Interval] with
  extension (x: Interval)
    def +(y: Interval): Interval = Interval.make(x.lb + y.lb, x.ub + y.ub)
    def -(y: Interval): Interval = Interval.make(x.lb - y.ub, x.ub - y.lb)
    def *(y: Interval): Interval = (x, y) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) =>
        val arr = List[Double](lb1 * lb2, lb1 * ub2, ub1 * lb2, ub1 * ub2)
        Interval.make(arr.min, arr.max)
    }
    def /(y: Interval): Interval =
      val rhs = y match {
        case Interval(lb2, ub2) if !(lb2 <= 0 && 0 <= ub2) =>
          Interval.make(1/ub2, 1/lb2)
        case Interval(lb2, 0) =>
          Interval.make(Double.NegativeInfinity, 1/lb2)
        case Interval(0, ub2) =>
          Interval.make(1/ub2, Double.PositiveInfinity)
        case  _ => Interval.make(Double.NegativeInfinity, Double.PositiveInfinity)
      }
      x * rhs

given IntervalArithAbsDomain: NumericalAbsDomain[Interval] with {}
