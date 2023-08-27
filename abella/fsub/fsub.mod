module fsub.

% Subtyping

sub S top.
sub T T.
sub S T :- sub S Q, sub Q T.
sub (arrow S1 S2) (arrow T1 T2) :- sub T1 S1, sub S2 T2.
sub (all S1 (x\ S2 x)) (all T1 (x\ T2 x)) :-
  sub T1 S1,
  pi x\ (sub x T1 => sub (S2 x) (T2 x)).

% Typing

typeof (abs T1 E) (arrow T1 T2) :-
  pi x\ typeof x T1 => typeof (E x) T2.
typeof (app E1 E2) T12 :-
  typeof E1 (arrow T1 T2),
  typeof T2 T1.
typeof (tabs T1 E) (all T1 T2) :-
  pi x\ sub x T1 => typeof (E x) (T2 x).
typeof (tapp E T2) (T12 T2) :-
  typeof E (all T11 T12),
  sub T2 T11.

% small-step reduction

value (abs T E).
value (tabs T E).

step (app (abs T E1) V2) (E1 V2) :- value V2.
step (tapp (tabs T1 E) T2) (E T2).
step (app E1 E2) (app E1' E2) :- step E1 E1'.
step (app V1 E2) (app V1 E2') :- value V1, step E2 E2'.
step (tapp E T) (tapp E' T) :- step E E'.