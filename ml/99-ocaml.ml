(* Write a function last : 'a list -> 'a option that returns the last element of a list. (easy) *)
let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t;;

(* Find the last but one (last and penultimate) elements of a list. (easy) *)
let rec last_two = function
  | [] | [_] -> None
  | [x; y] -> Some (x, y)
  | _::t -> last_two t;;

(* Find the k'th element of a list. (easy) *)
let rec at k = function
  | [] -> None
  | x::t -> if k = 1 then Some x else at (k-1) t;;

(* Find the number of elements of a list. (easy) *)
let rec length = function
  | [] -> 0
  | [_] -> 1
  | _::t -> 1 + length t;;

let length xs =
  let rec aux n = function
    | [] -> n
    | _::t -> aux (1+n) t
  in
    aux 0 xs;;

(* Reverse a list. (easy) *)
let reverse xs =
  let rec aux acc = function
    | [] -> acc
    | x::t -> aux (x::acc) t
  in
    aux [] xs;;

(* Find out whether a list is a palindrome. (easy) *)
let is_palindrome xs =
  xs = List.rev xs;;

(* flatten a nested list structure *)
type 'x node =
  | One of 'x
  | Many of 'x node list;;

let flatten xs = 
  let rec aux acc = function
    | [] -> acc
    | One x::t -> aux (acc @ [x]) t
    | Many x::t -> aux (List.append acc (aux [] x)) t
  in
    aux [] xs;;

let r = flatten [ One "a" ; Many [ One "b" ; Many [ One "c" ; One "d" ] ; One "e" ] ];;

(* eliminate consecutive duplicates of list eliments *)
let compress xs = 
  let rec aux acc = function
    | [] -> acc
    | x::t -> if List.length acc = 0 then aux (x::acc) t
              else if List.hd acc = x then aux acc t
              else aux (x::acc) t
  in
    List.rev (aux [] xs);;

let rec compress = function
  | a::(b::_ as t) -> if a = b then compress t else a :: compress t
  | smaller -> smaller
;;

(* Pack consecutive duplicates of list elements into sublists. *)
let pack xs =
  let rec aux current acc = function
    | [] -> []
    | [x] -> (x :: current) :: acc
    | a :: (b :: _ as t) ->
        if a = b then aux (a :: current) acc t
        else aux [] ((a :: current) :: acc) t in
  List.rev (aux [] [] xs)
;;
pack ["a";"a";"a";"a";"b";"c";"c";"a";"a";"d";"d";"e";"e";"e";"e"];;

(* Run-length encoding of a list. (easy) *)
let encode xs =
  let rec aux count acc = function
    | [] -> acc
    | [x] -> ((count + 1), x) :: acc
    | a :: (b :: _ as t) -> 
        if a = b then aux (count + 1) acc t
        else aux 0 (((count + 1), a) :: acc) t
  in
    List.rev (aux 0 [] xs)
;;

let encode list = 
  List.map (fun l -> (List.length l, List.hd l)) (pack list);;

(* Modified run-length encoding. (easy) *)
type 'a rle =
  | One of 'a
  | Many of int * 'a;;


