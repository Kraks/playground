package mutation

package plain {
  class Key

  def transiently[T](thunk: Key => T):
    T = thunk(new Key)

  class Cell[T](private var cell: T):
    type K <: Key
    def get: T = cell
    def set(v: T)(k: K) = cell = v
}

package usingImplicit {
  class Key

  def transiently[T](thunk: Key ?=> T):
    T = thunk(using new Key)

  class Cell[T](private var cell: T):
    type K <: Key
    def get: T = cell
    def set(v: T)(using k: K) = cell = v

  object Cell:
    def apply[T](v: T)(using k: Key): Cell[T]{type K = k.type} =
      new Cell[T](v){type K = k.type}
}

@main def main() = {
  import usingImplicit._

  val b1 = transiently:
    val b1 = Cell[Int](5) //{type K = k.type}
    b1.set(10) // OK --> k can be used to mutate the box.
    (b1, (v: Int) => b1.set(v))

  //val (b, k) = b1 // ERROR --> k is no longer in scope
  //val a = b.set(20)(k)
  val (x, wrx) = b1
  val _ = wrx(20)
  println(x.get)

  /*
  // this is a type error:
  val b2 = transiently: k =>
    val b1 = new Cell[Int](5){type K = k.type}
    b1.set(10)(k) // OK --> k can be used to mutate the box.
    (b1, k)
  val (y, k2) = b2
  y.set(20)(k2)
  */
}
