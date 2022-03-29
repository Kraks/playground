Require Import Classical.

Axiom classic : forall P : Prop, P \/ ~P.

Theorem peirce : forall P : Prop, ((P -> False) -> P) -> P.
Proof.
  intros P H.
  destruct (classic P).
  apply H0.
  apply H.
  apply H0.
Qed.

Theorem peirce1 : forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
  intros P Q H.
  destruct (classic P).
  - apply H0.
  - apply H.
    unfold not in H0.
    destruct (classic Q).
    + auto.
    + unfold not in H1.
      tauto.
Qed.

Inductive MyInd : term := ident|&: term|&.
