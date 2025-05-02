import Lake
open Lake DSL

package "theorem_proving_in_lean4" where
  -- add package configuration options here

lean_lib «TheoremProvingInLean4» where
  -- add library configuration options here
  -- require "leanprover-community" / "mathlib"

@[default_target]
lean_exe "theorem_proving_in_lean4" where
  root := `Main
