package compositional

// Definitions of lattice and numerical abstract domain

trait Lattice[T]:
  def bot: T
  def top: T
  extension (l1: T)
    def ⊑(l2: T): Boolean
    def ⊔(l2: T): T
    def ⊓(l2: T): T

trait AbsDomain[T: Lattice]:
  extension (l1: T)
    // widening
    def ▽(l2: T): T
    // narrowing
    def △(l2: T): T

trait Arith[A]:
  extension (a: A)
    def +(b: A): A
    def -(b: A): A
    def *(b: A): A
    def /(b: A): A

trait NumericalAbsDomain[T: Lattice : AbsDomain : Arith] {}

// Instances of built-in lattice structures

given IntLattice: Lattice[Int] with
  def bot: Int = Int.MinValue
  def top: Int = Int.MaxValue
  extension (l1: Int)
    def ⊑(l2: Int): Boolean = l1 <= l2
    def ⊔(l2: Int): Int = math.max(l1, l2)
    def ⊓(l2: Int): Int = math.min(l1, l2)

given DoubleLattice: Lattice[Double] with
  def bot: Double = Double.NegativeInfinity
  def top: Double = Double.PositiveInfinity
  extension (l1: Double)
    def ⊑(l2: Double): Boolean = l1 <= l2
    def ⊔(l2: Double): Double = math.max(l1, l2)
    def ⊓(l2: Double): Double = math.min(l1, l2)

given OptionLattice[T](using lt: Lattice[T]): Lattice[Option[T]] with
  def bot: Option[T] = None
  def top: Option[T] = Some(lt.top)
  extension (l1: Option[T])
    def ⊑(l2: Option[T]): Boolean = l1.getOrElse(lt.bot) ⊑ l2.getOrElse(lt.bot)
    def ⊔(l2: Option[T]): Option[T] =
      if (l1.isEmpty && l2.isEmpty) None
      else Some(l1.getOrElse(lt.bot) ⊔ l2.getOrElse(lt.bot))
    def ⊓(l2: Option[T]): Option[T] =
      if (l1.isEmpty || l2.isEmpty) None
      else Some(l1.getOrElse(lt.bot) ⊓ l2.getOrElse(lt.bot))

given OptionAbsDomain[T: Lattice : AbsDomain]: AbsDomain[Option[T]] with
  val lt = summon[Lattice[T]]
  extension (l1: Option[T])
    def ▽(l2: Option[T]): Option[T] =
      if (l1.isEmpty && l2.isEmpty) None
      else Some(l1.getOrElse(lt.bot) ▽ l2.getOrElse(lt.bot))
    def △(l2: Option[T]): Option[T] =
      if (l1.isEmpty || l2.isEmpty) None
      else Some(l1.getOrElse(lt.bot) △ l2.getOrElse(lt.bot))

given ProductLattice[A, B](using la: Lattice[A], lb: Lattice[B]): Lattice[(A, B)] with
  def bot: (A, B) = (la.bot, lb.bot)
  def top: (A, B) = (la.top, lb.top)
  extension (l1: (A, B))
    def ⊑(l2: (A, B)): Boolean = l1._1 ⊑ l2._1 && l1._2 ⊑ l2._2
    def ⊔(l2: (A, B)): (A, B) = (l1._1 ⊔ l2._1, l1._2 ⊔ l2._2)
    def ⊓(l2: (A, B)): (A, B) = (l1._1 ⊓ l2._1, l1._2 ⊓ l2._2)

given ProductAbsDomain[A: Lattice : AbsDomain, B: Lattice : AbsDomain]: AbsDomain[(A, B)] with
  extension (l1: (A, B))
    def ▽(l2: (A, B)): (A, B) = (l1._1 ▽ l2._1, l1._2 ▽ l2._2)
    def △(l2: (A, B)): (A, B) = (l1._1 △ l2._1, l1._2 △ l2._2)

given MapLattice[K, V](using lv: Lattice[V]): Lattice[Map[K, V]] with
  def bot: Map[K, V] = Map[K, V]()
  def top: Map[K, V] = throw new RuntimeException("No representation of top map")
  extension (m1: Map[K, V])
    def ⊑(m2: Map[K, V]): Boolean = {
      m1.foreach { case (k, v) =>
        if (!(v ⊑ m2.getOrElse(k, lv.bot))) return false
      }
      true
    }
    def ⊔(m2: Map[K, V]): Map[K, V] =
      m2.foldLeft(m1) { case (m, (k, v)) => m + (k -> v ⊔ m.getOrElse(k, lv.bot)) }
    def ⊓(m2: Map[K, V]): Map[K, V] =
      m1.keySet.intersect(m2.keySet).foldLeft(Map[K,V]()) { case (m, k) => m + (k -> m1(k) ⊓ m2(k)) }

given MapAbsDomain[K, V: Lattice : AbsDomain]: AbsDomain[Map[K, V]] with
  val lv = summon[Lattice[V]]
  extension (m1: Map[K, V])
    def ▽(m2: Map[K, V]): Map[K, V] =
      m2.foldLeft(m1) { case (m, (k, v)) => m + (k -> v ▽ m.getOrElse(k, lv.bot)) }
    def △(m2: Map[K, V]): Map[K, V] =
      m1.keySet.intersect(m2.keySet).foldLeft(Map[K,V]()) { case (m, k) => m + (k -> m1(k) △ m2(k)) }
