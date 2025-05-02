(* Representing queues as lists*)
structure Queue1 =
struct
  type 'a t = 'a list;
  exception E;

  val empty = [];

  fun enq(q, x) = q @ [x];

  fun null(x::q) = false
    | null _     = true;

  fun hd(x::q) = x
    | hd []    = raise E;

  fun deq(x::q) = q
    | deq []   = raise E;
end;

Queue1.deq ["We", "happy", "few"];

(* Representing Queue as new Datatype *)
structure Queue2 =
struct
  datatype 'a t = empty
                | enq of 'a t * 'a;
  exception E;

  fun null (enq _) = false
    | null empty   = true;

  fun hd (enq(empty, x)) = x
    | hd (enq(q, x))     = hd q
    | hd empty           = raise E;

  fun deq (enq(empty, x)) = empty
    | deq (enq(q, x))     = enq(deq q, x)
    | deq empty           = raise E;
end;

val q = Queue2.enq(Queue2.enq(Queue2.empty, "3"), "a");

(* Representing queues as pairs of lists *)
structure Queue3 = 
struct
  datatype 'a t = Queue of ('a list * 'a list);
  exception E;

  val empty = Queue([], []);

  fun norm (Queue([], tails)) = Queue(rev tails, [])
    | norm q                  = q;

  fun null(Queue([], [])) = true
    | null _              = false;

  fun hd(Queue(x::_, _)) = x
    | hd(Queue([], _))   = raise E;

  fun enq(Queue(heads, tails), x) = norm(Queue(heads, x::tails));

  fun deq (Queue(x::heads, tails)) = norm(Queue(heads, tails))
    | deq (Queue([], _))           = raise E;

end;

val q = Queue3.enq(Queue3.empty, 3);
val q = Queue3.enq(q, 4);
val q = Queue3.enq(q, 5);

signature QUEUE = 
sig
  type 'a t
  exception E
  val empty : 'a t
  val enq   : 'a t * 'a -> 'a t
  val deq   : 'a t -> 'a t
  val null  : 'a t -> bool
  val hd    : 'a t -> 'a
end;

(* Use : for transparent signature *)

structure S1 : QUEUE = Queue1;
structure S2 : QUEUE = Queue2;
structure S3 : QUEUE = Queue3;

(* Use :> for opaque signature *)
structure AbsQ1 :> QUEUE = Queue1;
structure AbsQ2 :> QUEUE = Queue2;
structure AbsQ3 :> QUEUE = Queue3;

val q = AbsQ3.enq(AbsQ3.empty, 3);

(* These two ways provide a all-or-nothing choice, which is not flexible enough *)

(* abstype DB with D end *)

abstype 'a queue1 = Q1 of 'a list
  with
  val empty = Q1 [];
  
  fun enq(Q1 q, x) = Q1 (q @ [x]);

  fun qnull(Q1[x::q]) = false
    | qnull _         = true;

  fun qhd(Q1(x::q)) = x;
  
  fun deq(Q1(x::q)) = Q1 q;
end;

abstype 'a queue2 = Empty
                  | Enq of 'a queue2 * 'a
  with
  val empty = Empty
  and enq = Enq

  fun qnull(Enq _) = false
    | qnull Empty  = true;

  fun qhd (Enq(Empty, x)) = x
    | qhd (Enq(q, x)) = qhd q;

  fun deq (Enq(Empty, x)) = Empty
    | deq (Enq(q, x)) = Enq(deq q, x);

end;


