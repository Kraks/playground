import Mathlib.Data.Finset.Sort

@[simp]
def indexr {X : Type} (n : ℕ) (l : List X) : Option X :=
  match l with
  | [] => none
  | a :: l' => if n == l'.length then some a else indexr n l'

lemma indexrSome : ∀ {A} (xs : List A) i,
  i < xs.length -> ∃ x, indexr i xs = some x := by
  intro A xs i h; induction xs
  case nil => simp at h
  case cons x xs ih =>
    simp; by_cases h': i = xs.length
    . simp [h']
    . simp [if_neg h']; apply ih; simp at h; omega

lemma indexrSome' : ∀ {A} (xs : List A) i,
  (∃ x, indexr i xs = some x) → i < xs.length := by
  intros A xs i h; induction xs
  case nil => simp at h
  case cons x xs ih =>
    simp at h; by_cases h': i = xs.length
    . subst h'; simp
    . simp [if_neg h'] at h; simp;
      have h' := ih h; omega

lemma indexrHead : ∀ {A} (x : A) (xs : List A),
  indexr xs.length (x :: xs) = some x := by intros A x xs; simp
