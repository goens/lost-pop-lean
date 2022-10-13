import Pop.Exploration
import Pop.Arch.ARM
import Litmus.ARM

open Pop ARM

def main : IO Unit := do

  println! "running ARM 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.arm_2
  println! printMultipleLitmusResults mp_litmus (printWitnesses := false)

  println! "running ARM 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.arm_3 (maxIterations := some 20000)
  println! printMultipleLitmusResults mp_litmus (printWitnesses := false)

/-
  println! "running ARM 4-thread (IRIW) tests"
  let iriw_litmus := runMultipleLitmus Litmus.arm_4  (logProgress := true)
  for (test,res) in Litmus.arm_4.zip iriw_litmus do
    println! prettyPrintLitmusResult test res
-/
