fun square x = x * x;

fun cube(x: real) = x * x * x;

fun title(name) = "The Duck of " ^ name;

type vec = real * real;

fun lengthvec(x, y) = Math.sqrt(x*x + y*y);

fun negvec(x, y): vec = (~x, ~y);

fun addvec((x1, y1), (x2, y2)): vec = (x1+x2, y1+y2);

fun subvec(v1, v2) = addvec(v1, negvec v2);

fun distance(v1, v2) = lengthvec(subvec(v1, v2));
(* 
fun distance(pairv) = lengthvec(subvec pairv);
*)

fun scalevec(r, (x, y)): vec = (r * x, r * y);

val henryV = {name = "Henry V",
              born = 1387,
              crowned = 1413,
              died = 1422,
              quote = "Bid then achieve me and then sell my bones" };
val {name = nameV, born = bornV, ...} = henryV;

type king = {name: string,
             born: int,
             crownen: int,
             died: int,
             quote: string};

fun lifetime(k: king) = #died k - #born k;
fun lifetime2({born, died,...}: king) = died - born;

(* default 0 *)
infix xor;
fun (p xor q) = (p orelse q) andalso not (p andalso q);

infix 6 plus;
fun (a plus b) = "(" ^ a ^ "+" ^ b ^ ")";

infix 7 times;
fun (a times b) = "(" ^ a ^ "*" ^ b ^ ")";
(* infixr *)

infix 8 pow;
fun (a pow b) = "(" ^ a ^ "^" ^ b ^ ")";

infix ++;
fun ((x1, y1) ++ (x2, y2)): vec = (x1+x2, y1+y2);

op^("a", "b");
nonfix ++;

fun fact n = if n = 0 then 1 else n * fact(n-1);

fun facti(n, p) = if n = 0 then p else facti(n-1, n*p);

fun even n = (n mod 2 = 0);

fun powoftwo n = (n=1) orelse (even(n) andalso powoftwo(n div 2));

fun gcd(m, n) = if (m=0) then n else gcd(n mod m, m);

(* power(x, k)
*  x^1 = x
*  x^2n = (x^2)^n
*  x^(2n+1) = x * (x^2)^n
*)
fun power(x, k): real = 
  if k = 1 then x
  else if k mod 2 = 0 then power(x*x, k div 2)
                      else x * power(x*x, k div 2)

fun nextfib(prev, curr: int) = (curr, prev+curr);
fun fibpair(n) = if n = 1 then (0, 1) else nextfib(fibpair(n-1));

fun itfib(n, prev, curr): int = 
  if n=1 then curr
  else itfib(n-1, curr, prev+curr);
fun fib n = itfib(n, 0, 1);

fun increase(k, n) = if (k+1)*(k+1) > n then k else k+1;
fun introot n = if n = 0 then 0 else increase(2 * introot(n div 4), n);

fun fraction(n, d) = 
  let val com = gcd(n, d)
  in (n div com, d div com)
end;

fun sqroot a = 
let val acc = 1.0E~10
    fun findroot x = 
    let val nextx = (a/x + x)/2.0
    in if abs(x-nextx) < acc * x
       then nextx else findroot nextx
    end
in findroot 1.0 end;
