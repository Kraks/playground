fun upto (m, n) = 
  if m > n then [] else m :: upto(m+1, n)

fun prod [] = 1
  | prod (n :: ns) = n * prod(ns)

(* match nonexhaustive *)
fun maxl [m]: int = m
  | maxl (m :: n :: ns) = if m > n then maxl(m::ns)
                                   else maxl(n::ns)

fun factl n = prod(upto(1, n))

val clist = explode "Hello SML";
val str = implode clist;
concat ["Hello", "world"];

fun null [] = true
  | null (_ :: _) = false

fun hd (x :: _) = x
fun tl (_ :: xs) = xs

fun prod xs = if null xs then 1 else (hd xs) * (prod (tl xs));

fun nlength [] = 0
  | nlength (x :: xs) = 1 + nlength xs

fun nlength ns = 
let
    fun addlen (n, []) = n
    | addlen (n, x::l) = addlen(n+1, l)
in
    addlen(0, ns)
end
    
fun take ([], i) = []
  | take (x::xs, i) = if i > 0 then x::take(xs, i-1)
                      else []

fun rtake ([], _, taken) = taken
  | rtake (x::xs, i, taken) = 
    if i>0 then rtake(xs, i-1, x::taken)
    else taken

fun drop ([], _) = []
  | drop (x::xs, i) = if i > 0 then drop(xs, i-1) else x::xs

infixr 5 @
fun ([] @ ys) = ys
  | ((x:: xs) @ ys) = x :: (xs @ ys)

fun nrev [] = []
  | nrev (x::xs) = nrev(xs) @ [x]

fun revAppend ([], ys) = ys
  | revAppend (x::xs, ys) = revAppend (xs, x::ys)

fun nrev xs = revAppend(xs, [])

fun concat [] = []
  | concat (l::ls) = l @ concat ls

fun zip (x::xs, y::ys) = (x,y) :: zip(xs, ys)
  | zip _ = []

fun conspair ((x, y), (xs, ys)) = (x::xs, y::ys)
fun unzip [] = ([], [])
  | unzip (p::ps) = conspair(p, unzip ps);

fun unzip [] = ([], [])
  | unzip ((x, y) :: ps) = 
    let val (xs, ys) = unzip ps
    in (x::xs, y::ys) end

fun rev_unzip ([], xs, ys) = (xs, ys)
  | rev_unzip ((x, y)::pairs, xs, ys) = rev_unzip(pairs, x::xs, y::ys)

fun change (coinval, 0) = []
| change (c::coinval, amount) = 
  if amount < c then change (coinval, amount)
  else c :: change(c::coinval, amount-c)

(* TODO Binary Arithmitic *)

fun headcol [] = []
  | headcol ((x::_)::rows) = x :: headcol rows

fun tailcols [] = []
  | tailcols ((_::xs)::rows) = xs :: tailcols rows

fun transp ([] :: rows) = []
  | transp rows = headcol rows :: transp (tailcols rows)

infix mem;
fun (x mem []) = false
  | (x mem (y::ys)) = (x=y) orelse (x mem ys)

fun newmem (x, xs) = if x mem xs then xs else x::xs

fun setof [] = []
  | setof (x::xs) = newmem(x, setof xs);

setof([1, 2, 2, 3]);
newmem(1, setof [2, 2, 3]);
newmem(1, newmem(2, setof [2, 3]));
newmem(1, newmem(2, newmem(2, setof [3])));
newmem(1, newmem(2, newmem(2, newmem(3, setof []))));
newmem(1, newmem(2, newmem(2, [3])));
newmem(1, newmem(2, [2, 3]));
newmem(1, [2, 3]);

(* union of two sets *)
fun union ([], ys) = ys
  | union (x::xs, ys) = newmem(x, union(xs, ys))

(* Intersection of two sets *)
fun inter ([], ys) = ys
  | inter (x::xs, ys) = if x mem ys then x::inter(xs, ys)
			else inter(xs, ys);

infix subs;
fun ([] subs ys) = true
  | ((x::xs) subs ys) = (x mem ys) andalso (xs subs ys);

infix seq;
(* sets equal *)
fun (xs seq ys) = (xs subs ys) andalso (ys subs xs);

fun powset ([], base) = [base]
  | powset (x::xs, base) = powset(xs, base) @ powset(xs, x::base);

powset([1, 2], []);
powset([2], []) @ powset([2], [1]);
powset([], []) @ powset([], [2]) @ powset([], [1]) @ powset([], [2,1]);

fun cartprod ([], ys) = []
  | cartprod (x::xs, ys) = 
    let val xsprod = cartprod(xs, ys)
        fun pairx [] = xsprod
          | pairx (y::ytail) = (x, y) :: (pairx ytail)
    in pairx ys end;

fun assoc ([], a) = []
  | assoc ((x, y)::pairs, a) = if a=x then [y] else assoc(pairs, a);

(* GRAPH *)

val graph1 = [("a", "b"), ("a", "c"), ("a", "d"),
              ("b", "e"), ("c", "f"), ("d", "e"),
              ("e", "f"), ("e", "g")];

fun nexts (a, []) = []
  | nexts (a, (x, y)::pairs) = if a=x then y::nexts(a, pairs)
                               else nexts(a, pairs);

fun depth ([], graph, visited) = rev visited
  | depth (x::xs, graph, visited) =
    if x mem visited then depth (xs, graph, visited)
    else depth(nexts(x, graph) @ xs,  graph, x::visited);

fun breadth ([], graph, visited) = rev visited
  | breadth (x::xs, graph, visited) =
    if x mem visited then breadth(xs, graph, visited)
    else breadth(xs @ nexts(x, graph), graph, x::visited);

fun depth args =
let fun rdepth ([], graph, visited) = visited
      | rdepth (x::xs, graph, visited) = 
        rdepth (xs, graph, if x mem visited then visited
                           else rdepth(nexts(x, graph), graph, x::visited))
in rev(rdepth args) end;

val gworks = [("wake", "shower"), ("shower", "dress"), ("dress", "go"),
              ("wake", "eat"), ("eat", "washup"), ("washup", "go")];

fun topsort graph =
let
  fun sort ([], visited) = visited
      | sort (x::xs, visited) = 
        sort (xs, if x mem visited then visited else x::sort(nexts(x, graph),
                  visited))
  val (starts, _) = ListPair.unzip graph
in
  sort(starts, [])
end;

topsort([("a", "b"), ("b", "c")]);

fun pathsort graph =
let 
  fun sort ([], path, visited) = visited
    | sort (x::xs, path, visited) =
      if x mem path then hd[]
      else sort (xs, path, 
                 if x mem visited then visited else
                 x::sort(nexts(x, graph), x::path, visited))
  val (start, _) = ListPair.unzip graph
in
  sort(start, [], [])
end;

fun newvisit (x, (visited, cys)) = (x::visited, cys);

fun cyclesort graph = 
let
  fun sort ([], path, (visited, cys)) = (visited, cys)
    | sort (x::xs, path, (visited, cys)) = 
      sort (xs, path,
            if x mem path then (visited, x::cys)
            else if x mem visited then (visited, cys)
            else newvisit (x, sort(nexts(x, graph), x::path, (visited, cys))))
  val (starts, _) = ListPair.unzip graph
in
  sort(starts, [], ([], []))
end;

(* SORT *)

local val a = 16807.0 and m = 2147483647.0
in
  fun nextrand seed = 
    let val t = a * seed
    (* (a*seed) mod m *)
    in t - m * real(floor(t/m)) end
end;

fun randlist (n, seed, tail) = 
  if n = 0 then (seed, tail)
  else randlist(n-1, nextrand seed, seed::tail);

fun ins (x, []) = [x]
  | ins (x, y::ys) =
    if x <= y then x::y::ys
    else y::ins(x, ys);

fun insort [] = []
  | insort (x::xs) = ins(x, insort(xs));

fun quick [] = []
  | quick [x] = [x]
  | quick (a::bs) =
    let fun parition(left, right, []): real list = (quick left) @ (a::quick right)
          | parition(left, right, x::xs) =
            if x <= a then parition(x::left, right, xs)
            else parition(left, x::right, xs)
    in  parition([], [], bs) end;

fun merge ([], ys) = ys: real list
  | merge (xs, []) = xs
  | merge (x::xs, y::ys) =
    if x > y then y::merge(x::xs, ys)
    else x::merge(xs, y::ys);

(* top-down merge sort *)
fun mergesort [] = []
  | mergesort [x] = [x]
  | mergesort xs = 
    let val k = length xs div 2
    in merge(mergesort(List.take(xs, k)),
             mergesort(List.drop(xs, k)))
    end;

(* an optimization of top-down merge sort *)
fun mergesort' xs = 
let
  fun sort (0, xs) = ([], xs)
    | sort (1, x::xs) = ([x], xs)
    | sort (n, xs) =
      let val (l1, xs1) = sort((n+1) div 2, xs)
          val (l2, xs2) = sort(n div 2, xs1)
      in (merge(l1, l2), xs2)
      end
  val (l, _) = sort(length xs, xs)
in l end;

(* bottom-up merge sort *)
fun mergepairs ([l], k) = [l]
  | mergepairs (l1::l2::ls, k) =
    if k mod 2 = 1 then l1::l2::ls
    else mergepairs(merge(l1, l2)::ls, k div 2);

fun sorting([], ls, k) = hd(mergepairs(ls, 0))
  | sorting(x::xs, ls, k) = sorting(xs, mergepairs([x]::ls, k+1), k+1);

sorting([7.0, 4.0, 1.0, 6.0], [[]], 0);
sorting([4.0, 1.0, 6.0], mergepairs([7.0]::[[]], 0+1), 0+1);
sorting([4.0, 1.0, 6.0], mergepairs([[7.0], []], 1), 1);
sorting([4.0, 1.0, 6.0], mergepairs([[7.0], []], 1), 1);
sorting([4.0, 1.0, 6.0], [[7.0], []], 1);
sorting([1.0, 6.0], mergepairs([4.0]::[[7.0], []], 1+1), 1+1);
sorting([1.0, 6.0], mergepairs([[4.0], [7.0], []], 2), 2);
sorting([1.0, 6.0], mergepairs(merge([4.0], [7.0])::[[]], 0), 2);
sorting([1.0, 6.0], mergepairs([[4.0, 7.0], []], 0), 2);
sorting([1.0, 6.0], mergepairs(merge([4.0, 7.0], [])::[], 0), 2);
sorting([1.0, 6.0], [[4.0, 7.0]], 2);

(* Polynomial arithmetic *)
structure Poly =
struct
  type t = (int * real) list;
  val zero = [];
  fun sum ([], us) = us: t
    | sum (ts, []) = ts
    | sum ((m, a)::ts, (n, b)::us) =
      if m>n then (m,a)::sum(ts, (n,b)::us)
      else if n>m then (n,b)::sum((m, a)::ts, us)
      else
        if Real.==(a+b, 0.0) then sum(ts, us)
                             else (m, a+b)::sum(ts, us);

  fun termprod ((m, a), []) = []: t
    | termprod ((m, a), (n, b)::ts) =
      (m+n, a*b) :: termprod((m, a), ts);
  fun nprod ([], us) = []
    | nprod ((m, a)::ts, us) = sum(termprod((m, a), us),
                                   nprod(ts, us));

  fun prod ([], us) = []
    | prod ([(m, a)], us) = termprod((m, a), us)
    | prod (ts, us) =
      let
        val k = length ts div 2
      in 
        sum(prod(List.take(ts, k), us),
            prod(List.drop(ts, k), us))
      end;

  fun diff (ts, us) = sum(ts, termprod((0, ~1.0), us));

  (* TODO *)
  fun quorem (ts, (n,b)::us) =
  let fun dividing ([], qs) = (rev qs, [])
        | dividing ((m,a)::ts, qs) = 
           if m<n then (rev qs, (m,a)::ts)
           else dividing (sum(ts, termprod((m-n, ~a/b), us)),
                          (m-n, a/b)::qs)
  in dividing(ts, []) end;

  fun gcd ([], us) = us
    | gcd (ts, us) = gcd (#2(quorem(us, ts)), ts);
end;

Poly.sum([(3, 3.0), (0, 5.0)], [(2, 2.0), (0, 3.0)]);
Poly.sum([(3, 3.0), (2, 1.0), (0, 5.0)], [(3, 3.0), (0, 1.0)]);
Poly.sum([(3, 3.0), (2, 1.0), (0, 5.0)], [(2, 2.0), (0, 1.0)]);

val p1 = [(1, 1.0), (0, 1.0)]
and p2 = [(2, 1.0), (0, ~2.0)];
val xminus1 = [(1, 1.0), (0, ~1.0)];
Poly.quorem(p2, xminus1);


