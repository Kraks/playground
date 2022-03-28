(* CPS Hierarchy *)
open SMLofNJ.Cont

signature SHIFT_RESET = 
sig
  type answer
  val reset : (unit -> answer) -> answer
  val shift : (('a -> answer) -> answer) -> 'a
  type 'a gcont
  val replace_gcont : 'a gcont -> ('b gcont -> 'a) -> 'b
  val cont2gcont : 'a cont -> 'a gcont
end

structure innermost_level :> SHIFT_RESET = 
struct
  exception InnermostLevelNoControl
  type answer = unit
  type 'a gcont = 'a cont
  fun replace_gcont new_c e_thunk = 
    callcc (fn old_c => throw new_c (e_thunk old_c))
  fun cont2gcont c = c
  fun reset _ = raise InnermostLevelNoControl
  fun shift _ = raise InnermostLevelNoControl
end

functor sr_outer (type ans 
                  structure inner : SHIFT_RESET) :> SHIFT_RESET
where type answer = ans =
struct
  exception MissingReset
  exception Fatal
  type answer = ans
  type 'a gcont = (answer inner.gcont) list * 'a inner.gcont
  val stack = ref [] : (answer inner.gcont) list ref
  fun replace_gcont (new_ks, new_k) e_thunk =
    inner.replace_gcont new_k
    (fn cur_k => let val cur_gcont = (!stack, cur_k)
                 in stack := new_ks; (e_thunk cur_gcont) end)
  fun cont2gcont action = ([], inner.cont2gcont action)
  fun popcc v = case !stack of
                  [] => raise Fatal
                | k'::ks => (stack := ks; inner.replace_gcont k' (fn _ => v))
  val id_popcc = inner.cont2gcont (isolate popcc)
  fun pushcc k e_thunk = inner.replace_gcont k
    (fn k' => (stack := k' :: !stack; e_thunk ()))
  fun reset e_thunk = pushcc id_popcc e_thunk
  fun shift k_abs = case !stack of
                      [] => raise MissingReset
                    | _ => inner.replace_gcont id_popcc
                            (fn (k : 'a inner.gcont)
                              => k_abs (fn w => pushcc k (fn () => w)))
end

functor ShiftReset (type ans) : SHIFT_RESET =
  sr_outer (type ans = ans
            structure inner = innermost_level)

functor ShiftResetNext = sr_outer

structure C1 = ShiftReset (type ans = int)
structure C2 = ShiftResetNext (type ans = bool
                               structure inner = C1)
