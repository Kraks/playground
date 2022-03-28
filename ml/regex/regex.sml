datatype regexp = ZERO
                | ONE
                | CHAR of char
                | CAT of regexp * regexp
                | SUM of regexp * regexp
                | STAR of regexp;

(* accept : regex * char list * (char list -> bool) -> bool *)
fun accept (r, s, k)
    = (case r of
           ZERO => false
         | ONE => k s
         | CHAR c =>
           (case s of (c'::s') => c = c' andalso k s'
                    | nil => false)
         | CAT (r1, r2) => accept (r1, s, fn s' => accept (r2, s', k))
         | SUM (r1, r2) => accept (r1, s, k) orelse accept (r2, s, k)
         | STAR r' => accept_star (r', s, k))
(* accept_star : regex * char list * *char list -> bool) -> bool *)
and accept_star (r, s, k)
    = k s
      orelse accept (r, s, fn s' => not (s = s')
                                    andalso accept_star (r, s', k));

(* match : regex * char list -> bool *)
fun match (r, s) = accept (r, s, fn s' => s' = nil);

(* Defunctionalized Regex Matcher *)

datatype regex_stack = EMPTY
                     | ACCEPT of regexp * regex_stack
                     | ACCEPT_STAR of char list * regexp * regex_stack;

(* accept_def : regexp * char list * regexp_stack -> bool *)
fun accept_def (r, s, k)
    = (case r of
           ZERO => false
         | ONE => pop_and_accept (k ,s)
         | CHAR c => (case s of (c'::s') => c = c' andalso pop_and_accept (k, s')
                              | nil => false)
         | CAT (r1, r2) => accept_def (r1, s, ACCEPT (r2, k))
         | SUM (r1, r2) => accept_def (r1, s, k) orelse accept_def (r2, s, k)
         | STAR r' => accept_star_def (r', s, k))
(* accept_star_def : regexp * char list * regexp_stack -> bool *)
and accept_star_def (r, s, k)
    = pop_and_accept (k, s)
      orelse accept_star_def (r, s, ACCEPT_STAR (s, r, k))
(* pop_and_accept : regexp_stack * char list *)
and pop_and_accept (EMPTY, s') = s' = nil
  | pop_and_accept (ACCEPT (r2, k), s') = accept_def(r2, s', k)
  | pop_and_accept (ACCEPT_STAR (s, r, k), s') = not (s = s')
                                                 andalso accept_star_def (r, s', k);

fun match_def (r, s) = accept_def (r, s, EMPTY);

let val r1 = match     (CAT (CHAR #"a", CHAR #"b"), [#"a", #"b"])
    val r2 = match_def (CAT (CHAR #"a", CHAR #"b"), [#"a", #"b"])
in print ((Bool.toString r1) ^ "\n");
   print ((Bool.toString r2) ^ "\n")
end;

