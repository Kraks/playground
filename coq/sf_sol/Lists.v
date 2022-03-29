Require Export Induction.

Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.
  
Check (pair 3 5).

Definition fst (p : natprod) : nat :=
match p with
| pair x y => x
end.

(* Pairs of Numbers *)

Definition snd (p : natprod) : nat :=
match p with
| pair x y => y
end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
match p with
| (x,y) => x
end.

Definition snd' (p : natprod) : nat :=
match p with
| (x,y) => y
end.

Definition swap_pair (p : natprod) : natprod := 
match p with
| (x, y) => (y, x)
end.

Theorem surjective_pairing' : forall n m : nat,
  (n, m) = (fst (n, m), snd (n, m)).
Proof.
  simpl. (* simpl is optional *)
  reflexivity.
Qed.

Theorem surjective_pairing : forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [p1 p2].
  simpl.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall p : natprod,
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [p1 p2].
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall p : natprod,
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [p1 p2].
  reflexivity.
Qed.

(* Lists of Numbers *)

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Check mylist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: 2 :: 3 :: nil.
Definition mylist2 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
match count with
| O => nil
| S count' => n :: (repeat n count')
end.

Fixpoint length (l : natlist) : nat :=
match l with
| nil => O
| x::xs => S (length xs)
end.

Fixpoint append (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | x::xs => x::(append xs l2)
  end.
  
Notation "x ++ y" := (append x y)
                     (right associativity, at level 60).

Example test_app1 : [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2 : nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

(* Head and Tail *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | x::xs => x
  end.
  
Definition tl (l : natlist) : natlist :=
  match l with 
  | nil => nil
  | x::xs => xs
  end.
  
Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2 : hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl : tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* Exercises *)

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | 0::xs => nonzeros xs
  | x::xs => x :: (nonzeros xs)
  end.

Example test_nonzeros : nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | nil => nil
  | x::xs => if evenb x then oddmembers xs
                        else x :: (oddmembers xs)
  end.

Example test_oddmembers : oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
  match l with
  | nil => O
  | x::xs => if evenb x then countoddmembers xs else S (countoddmembers xs)
  end.
  
Example test_countoddmembers1 : countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2 : countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3 : countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, nil => nil
  | nil, xs => xs
  | xs, nil => xs
  | (x::xs), (y::ys) => x::y::(alternate xs ys)
  end.
  
Example test_alternate1 : alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2 : alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3 : alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4 : alternate [] [2;3] = [2;3].
Proof. reflexivity. Qed.

(* Bags via Lists *)

Definition bag := natlist.

(* Exercises *)

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with 
  | nil => 0
  | x::xs => if beq_nat x v then S (count v xs) else count v xs
  end.

Example test_count1 : count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2 : count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := append.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  match beq_nat (count v s) O with
  | true => false
  | false => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
match s with 
| nil => nil
| x::xs => if beq_nat x v then xs else x::(remove_one v xs)
end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
match s with
| nil => nil
| x::xs => if beq_nat x v then remove_all v xs else x::(remove_all v xs)
end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
match s1 with
| nil => true
| x::xs => if member x s2 then subset xs (remove_one x s2) else false
end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(* Reasoning About Lists *)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof.
  intros l.
  reflexivity. 
Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l.
  - reflexivity.
  - reflexivity.
Qed.

(* Induction on Lists *)

Theorem append_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Fixpoint reverse (l : natlist) : natlist :=
match l with
| nil => nil
| x::xs => reverse xs ++ [x]
end.

Example test_rev1 : reverse [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Theorem append_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (reverse l) = length l.
Proof.
  intros l.
  induction l as [| n l1 IHl'].
  - reflexivity.
  - simpl. rewrite append_length. rewrite -> IHl'. 
    rewrite plus_comm. simpl. reflexivity.
Qed.

(* List Exercises Part 1*)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| n l1].
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Theorem rev_app_distr : forall l1 l2 : natlist,
  reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite append_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  reverse (reverse l) = l.
Proof.
  intros l.
  induction l as [| n l'].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite append_assoc.
  rewrite append_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  - simpl. reflexivity.
  - simpl. rewrite IHl1'. 
    induction n as [|n'].
    + reflexivity.
    + simpl. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool := 
match l1, l2 with
  | (x::xs), (y::ys) => if beq_nat x y then beq_natlist xs ys else false
  | [], [] => true
  | _, _ => false
end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 : (beq_natlist [1;2;3] [1;2;3] = true).
Proof. reflexivity. Qed.

Example test_beq_natlist3 : (beq_natlist [1;2;3] [1;2;4] = false).
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l : natlist,
  true = beq_natlist l l.
Proof.
  intros l.
  induction l as [| n l'].
  - reflexivity. 
  - simpl. rewrite <- beq_nat_refl. rewrite <- IHl'. reflexivity.
Qed.

(* List Exercises, Part 2 *)

Theorem count_member_nonzero : forall s : bag,
  leb 1 (count 1 (1::s)) = true.
Proof.
  intros s.
  induction s as [| n l'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem ble_n_Sn : forall n : nat,
  leb n (S n) = true.
Proof.
  intros n.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_decreases_count : forall s : bag,
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.
  induction s as [| n s'].
  - simpl. reflexivity.
  - induction n as [| n'].
    + simpl. rewrite ble_n_Sn. reflexivity.
    + simpl. rewrite IHs'. reflexivity.
Qed.

(* TODO Write down an interesting theorem bag_count_sum about
   bags involving the functions count and sum, and prove it. *)

Theorem rev_injective : forall l1 l2 : natlist,
  reverse l1 = reverse l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

(* Options *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(* Exercises *)

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | x::xs => Some x
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l : natlist) (d : nat),
  hd d l = option_elim d (hd_error l).
Proof.
  intros l.
  induction l as [| n l'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

End NatList.

(* Partial Maps *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x y : id) :=
  match x, y with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intros x.
  induction x. simpl.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map)
                  (x : id) (value : nat) : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y n d' => if beq_id x y then Some n else find x d'
  end.

(* Exercises *)

Theorem update_eq : forall (d : partial_map) (x : id) (v : nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. rewrite <- beq_id_refl. reflexivity.
Qed.

Theorem update_neq : forall (d : partial_map) (x y : id) (o : nat),
  beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros H.
  simpl. rewrite -> H. reflexivity.
Qed.

End PartialMap.

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.
