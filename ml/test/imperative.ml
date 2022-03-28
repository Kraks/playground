let add_polynom p1 p2 =
  let n1 = Array.length p1
  and n2 = Array.length p2 in
  let result = Array.create (max n1 n2) 0 in
  for i = 0 to n1 - 1 do result.(i) <- p1.(i) done;
  for i = 0 to n2 - 1 do result.(i) <- result.(i) + p2.(i) done;
  result
;;

add_polynom [| 1; 2 |] [| 1; 2; 3 |];;

let fact n =
  let result = ref 1 in
  for i = 2 to n do 
    result := i * !result
  done;
  !result
;;

type 'a ref = { mutable contents: 'a}

let ref x = {contents = x}
let (!) r = r.contents
let (:=) r x = r.contents <- x

let permuate array =
  let length = Array.length array in
  for i = 0 to length - 2 do
    let j = i + Random.int (length - i) in
    let tmp = array.(i) in
    array.(i) <- array.(j);
    array.(j) <- tmp
  done
;;
