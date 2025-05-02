type var = VZ | VS of var
type exp = V of var | B of bool | L of exp | A of exp * exp
type u = UB of bool | UA of (u -> u)

let rec lookup (x::env) = function
  | VZ -> x
  | VS v -> lookup env v

let rec eval env = function
  | V v -> lookup env v
  | B b -> UB b
  | L e -> UA (fun x -> eval (x::env) e)
  | A (e1, e2) -> match (eval env e1) with UA f -> f (eval env e2)

let test1 = A (L (V VZ), B true)
let test1r = eval [] test1
