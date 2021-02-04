package types

object Union {
  // Type negation
  type ¬[A] = A => Nothing
  // Type disjunction
  type ∨[T, U] = ¬[¬[T] with ¬[U]]
  type ¬¬[A] = ¬[¬[A]]
  // `<:<` demands that ¬¬[X] is subtype of (T ∨ U)
  type |∨|[T, U] = { type λ[X] = ¬¬[X] <:< (T ∨ U) }

  def size[T: (Int |∨| String)#λ](t: T) = t match {
    case i: Int => i
    case s: String => s.length
  }
  println(size(3))
  println(size("hello"))
}

