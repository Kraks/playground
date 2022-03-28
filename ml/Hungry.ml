type intlist = Empty
             | Cons of int * intlist

type hungry = { f : (int -> hungry); }

let rec hf (n : int) : hungry = { f = hf; }
