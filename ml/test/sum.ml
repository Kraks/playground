let rec sum xs =
  match xs with
    | [] -> 0
    | x :: xs' -> x + sum xs';;

sum [1; 2; 3; 4; 5; 6];;
