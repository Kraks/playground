Set Warnings "-notation-overridden,-parsing".
Require Import Utf8.

Definition idmap A := fun x : A => x.

Definition compose {A B C} (f : B -> C) (g : A -> B) (x : A) := f (g x).

Notation "f '∘' g" := (compose f g) (left associativity, at level 37).

Inductive paths {A} : A -> A -> Type :=
  idpath : ∀ x, paths x x.

Notation "x '↝' y" := (paths x y) (at level 70).

Hint Resolve @idpath.

Definition concat {A} {x y z : A} : (x ↝ y) → (y ↝ z) → (x ↝ z).
Proof.
  intros p q. induction p. induction q. apply idpath.
Defined.

Notation "p @ q" := (concat p q) (at level 60).

Definition opposite {A} {x y : A} : (x ↝ y) → (y ↝ x).
Proof.
  intros p. induction p. apply idpath.
Defined.

Notation "! p" := (opposite p) (at level 50).

Ltac path_induction :=
  intros; repeat progress (
                   match goal with
                   | [p : _ ↝ _ |- _ ] => induction p
                   | _ => idtac
                   end);
  auto.

Lemma idpath_left_unit A (x y : A) (p : x ↝ y) : (idpath x @ p) ↝ p.
Proof.
  intros. induction p. eapply idpath.
  (* path_induction *)
Defined.

Print idpath_left_unit.

Lemma idpath_right_unit A (x y : A) (p : x ↝ y) : (p @ idpath y) ↝ p.
Proof. path_induction. Defined.

Lemma opposite_right_inverse A (x y : A) (p : x ↝ y) : (p @ !p) ↝ idpath x.
Proof. path_induction. Defined.

Lemma opposite_left_inverse A (x y : A) (p : x ↝ y) : (!p @ p) ↝ idpath y.
Proof. path_induction. Defined.

Lemma opposite_concat A (x y z : A) (p : x ↝ y) (q : y ↝ z) : !(p @ q) ↝ !q @ !p.
Proof.
  induction p. induction q. eapply idpath.
Defined.

Lemma opposite_opposite A (x y : A) (p : x ↝ y) : !(! p) ↝ p.
Proof. path_induction. Defined.

Hint Resolve idpath_left_unit idpath_right_unit
     opposite_right_inverse opposite_left_inverse.

Lemma concat_associativity A (w x y z : A) (p : w ↝ x) (q : x ↝ y) (r : y ↝ z) :
  (p @ q) @ r ↝ p @ (q @ r).
Proof.
  induction p. induction q. induction r. eapply idpath.
Defined.

(* we call paths between paths homotopies. *)

Definition homotopy_concat A (x y z : A) (p p' : x ↝ y) (q q' : y ↝ z) :
  (p ↝ p') → (q ↝ q') → (p @ q ↝ p' @ q').
Proof.
  intros pp' qq'. induction p. induction q.
  induction pp'. induction qq'.
  eapply idpath.
Defined.

Lemma map {A B} {x y : A} (f : A → B) (p : x ↝ y) : f x ↝ f y.
Proof.
  induction p. eapply idpath.
Defined.

Lemma idpath_map A B (x : A) (f : A → B) : map f (idpath x) ↝ idpath (f x).
Proof.
  eapply idpath.
Defined.

Lemma concat_map A B (x y z : A) (f : A → B) (p : x ↝ y) (q : y ↝ z) :
  map f (p @ q) ↝ (map f p) @ (map f q).
Proof.
  induction p. induction q. eapply idpath.
Defined.

Lemma idmap_map A (x y : A) (p : x ↝ y) : map (idmap A) p ↝ p.
Proof.
  path_induction.
Defined.

Lemma composition_map A B C (f : A → B) (g : B → C) (x y : A) (p : x ↝ y) :
  map (g ∘ f) p ↝ map g (map f p).
Proof.
  path_induction.
Defined.

Lemma opposite_map A B (f : A → B) (x y : A) (p : x ↝ y) : !(map f p) ↝ map f (! p).
Proof.
  path_induction.
Defined.

Lemma map_cancel A B (f : A → B) (x y : A) (p q : x ↝ y) : p ↝ q → (map f p ↝ map f q).
Proof.
  intros pq.
  path_induction.
Defined.

Hint Resolve concat_map
     opposite_map map_cancel
     opposite_concat opposite_opposite
     homotopy_concat : path_hints.

Ltac path_tricks :=
  first
    [ apply homotopy_concat
    | apply opposite_map
    | apply opposite_opposite
    | apply opposite_concat
    | apply map_cancel
    | idtac]; auto with path_hints.

Ltac path_via x := apply @concat with (y := x); path_tricks.

Lemma map_naturality A (f : A → A) (p : ∀ x, f x ↝ x) (x y : A) (q : x ↝ y) :
  map f q @ p y ↝ p x @ q.
Proof.
  induction q.
  path_via (p x).
  - apply idpath_left_unit.
  - apply opposite. apply idpath_right_unit.
Defined.

Hint Resolve map_naturality : path_hints.