import STLC
import Lean

open IO

def main: IO Unit := do
  IO.println s!"Hello, cats!"
  let counter ← IO.mkRef 0
  let val1 ← counter.get
  IO.println s!"Initial value: {val1}"
  counter.modify (· + 1)
  let val2 ← counter.get
  IO.println s!"Updated value: {val2}"

#eval main
