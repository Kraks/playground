(* References:
 * Intensional Type Theory with Guarded Recursive Types qua Fixed Points on Universes
 * https://github.com/csgordon/guarded-recursion/blob/master/GuardedRec.v
 *)

Require Import Utf8.

(* later modality *)

Inductive later (T : Type) : Type :=
  next: T -> later T.

Arguments next [T] _.

Notation "▶ T" := (later T) (at level 50).

Definition lapp {A B : Type} (t1 : ▶ (A -> B)) (t2 : ▶ A) : ▶ B :=
  match t1, t2 with
  | next t', next u' => next (t' u')
  end.
Notation "t ⊛ u" := (lapp t u) (at level 49).

(* definitional equality *)

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C :=
  fun a => f (g a).

Notation "f ⋄ g" := (compose f g) (at level 55).

Lemma next_id : forall (T : Type) u, next (fun (x : T) => x) ⊛ u = u.
Proof.
  intros. destruct u. simpl. reflexivity.
Qed.

Lemma next_compose : forall (A B C : Type) s t u,
    ((next (@compose A B C) ⊛ s) ⊛ t) ⊛ u = s ⊛ (t ⊛ u).
Proof.
  intros. destruct s. destruct t. destruct u.
  simpl. unfold compose. reflexivity.
Qed.

Lemma next_app : forall (A B : Type) (t : A -> B) u,
    next t ⊛ next u = next (t u).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma next_right : forall (A B : Type) u (t : A),
    u ⊛ (next t) = next (fun (g : A -> B) => g t) ⊛ u.
Proof.
  intros. destruct u. simpl. reflexivity.
Qed.

(* Fixpoints *)

Axiom gfix : forall {A : Type}, ((▶ A) -> A) -> A.

Axiom gfix_red : forall {A : Type} (f : (▶ A) -> A), gfix f = f (next (gfix f)).
