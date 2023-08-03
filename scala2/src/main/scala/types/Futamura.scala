package types.futamura

trait Futamura {
  type P[_] // program representation type
  type M[_] // machine type

  /* To run a machine: */
  def run[A](ma: M[A]): A

  /* The specializer: a machine that
     takes a program representation of A => B,
     specializes it wrt a value of A, and
     yields a machine of M[B].
   */
  def specializer[A, B]: M[P[A => B] => A => M[B]]

  /* The program representation of specializer */
  def specializerProgram[A, B]: P[P[A => B] => A => M[B]]

  /* The interpreter: a machine that
     takes a program representation of A => B and a value of A,
     executes the program, and
     yields a value of B.
   */
  def interpreter[A, B]: M[P[A => B] => A => B]

  def abstractInterpreter[A, B, α[_]]: M[P[A => B] => α[A] => α[B]]

  /* The program representation of interpreter */
  def interpreterProgram[A, B]: P[P[A => B] => A => B]

  /* Yields executables */
  def firstProjection[A, B](prog: P[A => B]): M[A => B] =
    run(specializer[P[A => B], A => B])(interpreterProgram[A, B])(prog)

  def specializedSpecializerProgram[A, B]: P[A => B] => M[A => M[B]] =
    run(specializer[P[A => B], A => M[B]])(specializerProgram[A, B])

  /* A self-hosting specializer, ie a compiler */
  def secondProjection[A, B]: M[P[A => B] => M[A => B]] =
    specializedSpecializerProgram(interpreterProgram[A, B])

  /* A compiler-compiler, converting any interpreter to an equivalent compiler */
  def thirdProjection[A, B]: M[P[A => B] => M[A => M[B]]] =
    specializedSpecializerProgram(specializerProgram[A, B])

  /* The fourth projection is a quine */
  def quine[A, B]: M[P[A => B] => M[A => M[B]]] =
    run(thirdProjection[P[A => B], A => M[B]])(specializerProgram[A, B])
}

trait FutamuraAlt {
  // http://blog.sigfpe.com/2009/05/three-projections-of-doctor-futamura.html
  type P[_]
  type M[_]

  def run[A](ma: M[A]): A

  def specialize[A, B, C]: M[P[A ⇒ B ⇒ C] ⇒ A ⇒ M[B ⇒ C]]
  def specializeProgram[A, B, C]: P[P[A ⇒ B ⇒ C] ⇒ A ⇒ M[B ⇒ C]]
  def interpreter[A, B]: M[P[A ⇒ B] ⇒ A ⇒ B]
  def interpreterProgram[A, B]: P[P[A ⇒ B] ⇒ A ⇒ B]

  def firstProjection[A, B]: P[A ⇒ B] ⇒ M[A ⇒ B] =
    run(specialize[P[A ⇒ B], A, B])(interpreterProgram[A, B])
  def specializedSpecializeProgram[A, B, C]: P[A => B => C] => M[A => M[B => C]] =
    run(specialize[P[A => B => C], A, M[B => C]])(specializeProgram[A, B, C])
  def secondProjection[A, B, C]: M[P[A ⇒ B] ⇒ M[A ⇒ B]] =
    specializedSpecializeProgram(interpreterProgram[A, B])
  def thirdProjection[A, B, C]: M[P[A => B => C] => M[A => M[B => C]]] =
    specializedSpecializeProgram(specializeProgram[A, B, C])
}

trait FutamuraAlt1 {
  // From Matt Brown and Jens Palsberg's Specialization-safe Normalization
  type Rep[_]

  def unRep[A](x: Rep[A]): A
  def toRep[A](x: A): Rep[A]

  def mix[A, B]: Rep[A => B] => Rep[A] => Rep[B]
  def interp[A, B]: Rep[A => B] => A => B
  def compiler[A, B]: Rep[A] => Rep[B]

  def first[A, B](prog: Rep[Rep[A => B]]): Rep[A => B] = mix(toRep(interp[A, B]))(prog)
  def mixmix[A, B]: Rep[Rep[A => B]] => Rep[Rep[A] => Rep[B]] = mix(toRep(mix))
  def second[A, B](interp: Rep[A => B] => A => B): Rep[Rep[Rep[A => B]] => Rep[A => B]] = mixmix(toRep(toRep(interp)))
  def third[A, B]: Rep[Rep[Rep[A => B]] => Rep[Rep[A] => Rep[B]]] = mixmix(toRep(toRep(mix[A, B])))
  def fourth[A, B]: Rep[Rep[Rep[A => B]] => Rep[Rep[A] => Rep[B]]] =
    unRep(third[Rep[A => B], Rep[A] => Rep[B]])(toRep(toRep(mix[A, B])))

  def self_interp[A, B](p: Rep[A => B]): A => B
}

trait FutamuraAlt2 {
  type Rep[_]

  def toRep[A](x: A): Rep[A]
  def unRep[A](x: Rep[A]): A

  def mix[A, B]: Rep[A => B] => A => Rep[B]
  def interp[A, B]: Rep[A => B] => A => B
  def first[A, B](prog: Rep[A => B]): Rep[A => B] =
    mix[Rep[A => B], A => B](toRep(interp[A, B]))(prog)
  def mixmix[A, B]: Rep[A => B] => Rep[A => Rep[B]] = mix(toRep(mix[A, B]))
  def second[A, B]: Rep[Rep[A => B] => Rep[A => B]] = mixmix(toRep(interp[A, B]))
  def third[A, B]: Rep[Rep[A => B] => Rep[A => Rep[B]]] = mixmix(toRep(mix[A, B]))
  def fourth[A, B]: Rep[Rep[A => B] => Rep[A => Rep[B]]] = unRep(third[Rep[A => B], A => Rep[B]])(toRep(mix[A, B]))
}
