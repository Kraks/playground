module type Semantics = sig
  type ('c, 'dv) repr
  val int : int -> ('c, int) repr
  val bool : bool -> ('c, bool) repr
  val lam : (('c, 'da) repr -> ('c, 'db) repr) -> ('c, 'da -> 'db) repr
  val app : ('c, 'da -> 'db) repr -> ('c, 'da) repr -> ('c, 'db) repr
  val fix : ('x -> 'x) -> (('c, 'da -> 'db) repr as 'x)
  val add : ('c, int) repr -> ('c, int) repr -> ('c, int) repr
  val mul : ('c, int) repr -> ('c, int) repr -> ('c, int) repr
  val leq : ('c, int) repr -> ('c, int) repr -> ('c, bool) repr
  val if_ : ('c, bool) repr -> (unit -> 'x) -> (unit -> 'x)
    -> (('c, 'da) repr as 'x)
end

module Ex(S: Semantics) = struct
  open S
  let test1 () = app (lam (fun x -> x)) (bool true)
  let testpow () =
    lam (fun x -> fix (fun self -> lam (fun n ->
        if_ (leq n (int 0)) (fun () -> int 1)
          (fun () -> mul x (app self (add n (int (-1))))))))
  let pow7 = lam (fun x -> app (app (testpow ()) x) (int 7))
end

module R = struct
  type ('c, 'dv) repr = 'dv
  let int (x: int) = x
  let bool (b: bool) = b
  let lam f = f
  let app e1 e2 = e1 e2
  let fix f = let rec self n = f self n in self
  let add e1 e2 = e1 + e2
  let mul e1 e2 = e1 * e2
  let leq e1 e2 = e1 <= e2
  let if_ eb et ee = if eb then et() else ee()
end

module ExR = Ex(R);;

print_int (ExR.pow7 2);;
