(* http://www.cs.cmu.edu/~kw/research/reflect3.sml *)
(* Monadic reflection via callcc

   Based on Andrzej Filinski's thesis and his paper
   Representing monads, Proceedings POPL'99.

   Kevin Watkins
   October 2004 *)

signature REFLECT = sig
  type behavior
  val reflect : (('a -> behavior) -> behavior) -> 'a
  val reify : (unit -> behavior) -> behavior

  exception Embed
  val embed : unit -> ('a -> behavior) * (behavior -> 'a)
end

structure Reflect :> REFLECT = struct
  datatype void = Void of void
  val coerce = fn (x : void) => raise Match

  type behavior = unit -> void

  structure C = SMLofNJ.Cont
  (* (('a -> unit -> void) -> unit -> void) -> 'a *)
  fun reflect f = C.callcc (fn k => coerce (f (fn x => fn () => C.throw k x) ()))
  fun reify f = fn () => f () ()

  exception Embed
  val r = ref (fn x => raise Embed) : (exn -> void) ref
  fun 'a embed () =
    let exception E of 'a
    in (fn x => fn () => (!r)(E x),
        fn b => C.callcc (fn k =>
          let val s = (!r) in r := (fn E x => (r := s; C.throw k x)); coerce (b()) end))
    end
end

signature MONAD = sig
  type 'a t
  val unit : 'a -> 'a t
  val bind : ('a -> 'b t) -> 'a t -> 'b t
  val glue : (unit -> 'a t) -> 'a t
  val show : string t -> string
end

signature LINKAGE = sig
  val embed : unit -> ('a -> Reflect.behavior) * (Reflect.behavior -> 'a)
  val run : (unit -> string) -> string
end

signature REFLECT_MONAD = sig
  include MONAD
  include LINKAGE
  val reflect : 'a t -> 'a
  val reify : (unit -> 'a) -> 'a t
end

structure Base :> LINKAGE = struct
  val embed = Reflect.embed
  fun run t = t ()
end

functor ReflectMonad(structure M : MONAD
                     structure Link : LINKAGE)
        :> REFLECT_MONAD where type 'a t = 'a M.t = struct
  structure R = Reflect
  open M
  val (f : exn t -> R.behavior,
       g : R.behavior -> exn t) = Link.embed ()
  fun reflect m = R.reflect (fn k =>
    f (bind (fn a => glue (fn () => g (k a))) m))
  fun map f = bind (unit o f)
  fun 'a reify t =
    let exception E of 'a
    in map (fn E x => x) (glue (fn () => g (R.reify (f o unit o E o t))))
    end
  fun 'a embed () =
    let exception E of 'a
    in (f o unit o E,
        (fn E x => x) o reflect o g)
    end
  fun run t = Link.run (fn () => show (reify t))
end

structure ListR = ReflectMonad(
  structure Link = Base
  structure M = struct
    type 'a t = 'a list
    fun unit x = [x]
    fun bind f = foldr op@ nil o map f
    fun glue t = t ()
    fun show nil = "nil"
      | show (h :: t) = foldl (fn (s, t) => t^","^s) h t
  end)

structure NdR = ReflectMonad(
  structure Link = Base
  structure M = struct
    type 'a t = unit -> 'a list
    fun unit x = fn () => [x]
    fun bind f t = fn () => foldr op@ nil (map (fn x => f x ()) (t ()))
    fun glue t = fn () => t () ()
    fun show t = case t () of
                   nil => "<fail>"
                 | h::t => foldl (fn (s, t) => t^" <or> "^s) h t
  end)
