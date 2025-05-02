package compositional

// The Interval abstract domain

case class Interval(lb: Double, ub: Double) {
  def toConst: Option[Double] = if (lb == ub) Some(lb) else None
}

object Interval {
  def from(is: Int*): Interval = Interval(is.min.toDouble, is.max.toDouble)
}

given IntervalLattice(using ldb: Lattice[Double]): Lattice[Interval] with
  def bot = Interval(ldb.top, ldb.bot)
  def top = Interval(ldb.bot, ldb.top)
  extension (l1: Interval)
    def ⊑(l2: Interval) = (l1, l2) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) => lb2 ⊑ lb1 && ub1 ⊑ ub2
    }
    def ⊔(l2: Interval) = (l1, l2) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) ⇒ Interval(lb1 ⊓ lb2, ub1 ⊔ ub2)
    }
    def ⊓(l2: Interval) = (l1, l2) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) ⇒ Interval(lb1 ⊔ lb2, ub1 ⊓ ub2)
    }

given IntervalAbsDomain(using lit: Lattice[Interval]): AbsDomain[Interval] with
  extension (l1: Interval)
    def ▽(l2: Interval): Interval = (l1, l2) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) ⇒
        Interval(if (lb1 ⊑ lb2) lb1 else Double.NegativeInfinity,
                 if (ub2 ⊑ ub1) ub1 else Double.PositiveInfinity)
    }
    def △(l2: Interval): Interval = (l1, l2) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) ⇒
        Interval(if (lb1 == Double.NegativeInfinity) lb2 else lb1,
                 if (ub1 == Double.PositiveInfinity) ub2 else ub1)
    }

given IntervalArith: Arith[Interval] with
  extension (x: Interval)
    def +(y: Interval): Interval = (x, y) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) => Interval(lb1 + lb2, ub1 + ub2)
    }
    def -(y: Interval): Interval = (x, y) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) => Interval(lb1 - lb2, ub2 + ub1)
    }
    def *(y: Interval): Interval = (x, y) match {
      case (Interval(lb1, ub1), Interval(lb2, ub2)) =>
        val lb1lb2 = lb1 * lb2
        val lb1ub2 = lb1 * ub2
        val ub1lb2 = ub1 * lb2
        val ub1ub2 = ub1 * ub2
        val arr = List[Double](lb1lb2, lb1ub2, ub1lb2, ub1ub2)
        Interval(arr.reduce(math.min(_, _)), arr.reduce(math.max(_, _)))
    }
    def /(y: Interval): Interval =
      val rhs = y match {
        case Interval(lb2, ub2) if !(lb2 <= 0 && 0 <= ub2) =>
          Interval(1/ub2, 1/lb2)
        case Interval(lb2, 0) =>
          Interval(Double.NegativeInfinity, 1/lb2)
        case Interval(0, ub2) =>
          Interval(1/ub2, Double.PositiveInfinity)
        case  _ => Interval(Double.NegativeInfinity, Double.PositiveInfinity)
      }
      x * rhs

given IntervalArithAbsDomain: NumericalAbsDomain[Interval] with {}
