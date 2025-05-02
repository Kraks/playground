(* https://hol-theorem-prover.org/HOL-interaction.pdf *)

open arithmeticTheory listTheory;

Theorem less_add_1 :
  ∀n. n < n + 1
Proof
  decide_tac
QED

Theorem less_eq_mult:
  ∀n:num. n ≤ n * n
Proof
  Induct_on ‘n’
  >- decide_tac
  >- (asm_simp_tac bool_ss [MULT] >> decide_tac)
QED
        
