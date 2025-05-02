let square x = x * x;;

let rec fact x = 
  if x <= 1 then 1 else x * fact(x-1);;

let rec factorial x = 
  if (0 > x) then (raise Exit) else
  match x with
     0 -> 1
   | n -> (n * (factorial(n - 1)));;

let rec factorial x =
    if (x > x) then (raise Exit) else
    let rec helper x so_far = 
        match x with
          0 -> so_far
        | n -> (helper (n-1) (so_far * n))
    in
        (helper x 1);;

Printf.printf "Fact(5) is %d\n" (factorial 5);;
