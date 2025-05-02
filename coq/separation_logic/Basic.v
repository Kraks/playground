Set Implicit Arguments.
From SLF Require Import LibSepReference.
Import ProgramSyntax DemoPrograms.

Implicit Types n m : int.
Implicit Types p q : loc.

Definition incr : val :=
  <{ fun 'p =>
       let 'n = ! 'p in
       let 'm = 'n + 1 in
       'p := 'm }>.

Lemma triple_incr : forall (p : loc) (n : int),
    triple <{ incr p }>
      (p ~~> n)
        (fun _ => (p ~~> (n + 1))).
Proof.
  xwp.
