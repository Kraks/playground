(* 

Amodule.hello();;

*)

open Amodule
open Printf

(* hello();; *)

let () = hello ()
let my_data = ["a"; "beautiful"; "day"]
let () = List.iter (fun s -> printf "%s\n" s) my_data;;
