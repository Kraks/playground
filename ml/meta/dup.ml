open Runcode;;

let f x = .< .~x + .~x >.;;

let g x = .< let y = .~x in y + y >.;;

(* let g = (x => g x x) (square n2) *)
