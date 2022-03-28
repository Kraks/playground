open Runcode;;

let square x = x * x;;

let rec power n x = 
  if n = 0 then 1
  else if n mod 2 = 0 then square (power (n/2) x)
  else x * (power (n-1) x);;

let rec spower n x = 
  if n = 0 then .<1>.
  else if n mod 2 = 0 then .< square .~(spower (n/2) x) >.
  else .< .~x * .~(spower (n-1) x) >.;;

let spower7_code = .<fun x -> .~(spower 7 .<x>.)>.;;

let power3 = run .< fun x -> .~ (spower 3 .<x>.) >.;;

print_int (run spower7_code 3);;

print_int (power3 3);;

