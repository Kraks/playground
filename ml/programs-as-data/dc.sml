(* Functional Pearl: The Great Escape
 * Or, How to jump the border without getting caught
 *)

signature ESCAPE = 
sig
  type void
  val coerce : void -> 'a
  val escape : (('a -> void) -> 'a) -> 'a
end;

structure Escape : ESCAPE =
struct
  datatype void = VOID of void
  fun coerce (VOID v) = coerce v
  open SMLofNJ.Cont
  fun escape f = callcc (fn k => f (fn x => throw k x))
end;

signature CONTROL = 
sig
  type ans
  val shift : (('a -> ans) -> ans) -> 'a
  val reset : (unit -> ans) -> ans
end;

functor Control (type ans) : CONTROL =
struct
  open Escape
  exception MissingReset
  type ans = ans
  val mk : (ans -> void) ref = ref (fn _ => raise MissingReset)

  fun return x = coerce (!mk x)

  fun reset thunk = 
    escape (fn k => let val m = !mk in
                      mk := (fn r => (mk := m; k r));
                      return (thunk ())
                    end)

  fun shift f = escape (fn k => return (f (fn v => reset (fn () => coerce (k v)))))
end;
