import Pop
import Pop.Arch.Compound
import Litmus.Compound

open Pop Compound

def main : IO Unit := do
  println! "running Compound 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.compound_2
  println! printMultipleLitmusResults mp_litmus (printWitnesses := true)

  println! "running Compound 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.compound_3 (maxIterations := some 20000)
  println! printMultipleLitmusResults mp_litmus (printWitnesses := true)

/-
  println! "running Compound 4-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.compound_4
  println! printMultipleLitmusResults mp_litmus
-/
