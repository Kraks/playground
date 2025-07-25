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

lemma indexrSome'' : ∀ {A} (xs : List A) i,
  (∃ x, indexr i xs = some x) → (¬i = xs.length) := by
  intros A xs i h; have h'' := indexrSome' _ _ h; omega

lemma indexrHead : ∀ {A} (x : A) (xs : List A),
  indexr xs.length (x :: xs) = some x := by intros A x xs; simp

lemma indexrNone : ∀ {A} (xs : List A) i,
  i >= xs.length -> indexr i xs = none := by
  intros A xs i h; induction xs <;> simp
  case cons x xs ih =>
    simp at h; have h' : ¬ i = xs.length := by omega
    rw [if_neg h']; apply ih; omega

lemma indexrSkip : ∀ {A} (x: A) (xs : List A) i,
  (¬i = xs.length) → indexr i (x :: xs) = indexr i xs := by
  intros A x xs i h; simp; intros h'; omega

@[simp]
def update {X : Type} (l : List X) (n : ℕ) (x : X) : List X :=
  match l with
  | [] => []
  | a :: l' => if n == l'.length then x :: l' else a :: update l' n x

lemma updateLength : ∀ {A} (xs : List A) i x,
  xs.length = (update xs i x).length := by
  intros A xs i x; induction xs <;> simp
  case cons y ys ih =>
    by_cases h': i = ys.length
    . subst h'; simp
    . simp [if_neg h']; apply ih

lemma indexrUpdateHit : ∀ {A} (x : A) (xs : List A) i,
  i < xs.length → indexr i (update xs i x) = some x := by
  intros A x xs i h; induction xs <;> simp at h
  case cons y ys ih =>
    by_cases h': i = ys.length
    . subst h'; simp
    . simp [if_neg h']; simp [<- updateLength]; simp [if_neg h']
      apply ih; omega

lemma indexrUpdateMiss : ∀ {A} (xs : List A) i x j,
  j ≠ i → indexr j (update xs i x) = indexr j xs := by
  intros A xs i x j hij; induction xs <;> simp
  case cons y ys ih =>
    by_cases h': i = ys.length <;> by_cases h'' : j = ys.length
    . omega
    . rw [h', if_neg h'']; simp; intro; omega
    . rw [if_neg h', h'']; simp; intro hu; rw [<- updateLength] at hu; omega
    . rw [if_neg h', if_neg h'']; simp; rw [<- updateLength]; rw [if_neg h'']; apply ih
