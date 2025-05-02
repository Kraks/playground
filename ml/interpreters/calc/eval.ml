open Syntax

(*
let rec power x = function k ->
  if k = 1 then x
  else if k mod 2 = 0 then power (x * x) (k / 2)
       else x * power (x * x) (k / 2)
;;
*)

let rec power x = function k ->
  if k = 0 then 1
  else x * power x (k-1)
;;

let rec eval = function
  | Numeral n -> n
  | Plus (e1, e2) -> eval e1 + eval e2
  | Minus (e1, e2) -> eval e1 - eval e2
  | Times (e1, e2) -> eval e1 * eval e2
  | Divide (e1, e2) ->
      let n2 = eval e2 in
        if n2 <> 0 then eval e1 / n2 else failwith "Division by zero"
  | Negate e -> -(eval e)
  | Power (e1, e2) -> power (eval e1) (eval e2)

