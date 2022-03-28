let rec sigma f = function
  | [] -> 0
  | x :: l -> f x + sigma f l
;;

sigma (fun x -> x * x) [1; 2; 3];;

let compose f g = fun x -> f (g x);;

(* let square_o_fact = compse square fact;; *)

let rec power f n =
  if n = 0 then fun x -> x
  else compose f (power f (n - 1));;
