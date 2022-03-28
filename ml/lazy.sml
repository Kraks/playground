signature LAZY =
sig
  val lazy: (unit -> 'a) -> unit -> 'a
end

structure Lazy: LAZY =
struct
  fun lazy (th: unit -> 'a): unit -> 'a =
    let 
      datatype 'a lazy_result = Unevaluated of (unit -> 'a)
                              | Evaluated of 'a
                              | Failed of exn
      val r = ref (Unevaluated th)
    in
      fn () =>
        case !r of
          Unevaluated th => 
          let val a = th ()
            handle x => (r := Failed x; raise x)
            val () = r:= Evaluated a
          in a end
        | Evaluated a => a
        | Failed x => raise x
    end
end

