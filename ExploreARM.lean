import Pop
import Pop.Arch.ARM

open Pop ARM

def main : IO Unit := do
  println! "running ARM 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.arm_2
  for (test,res) in Litmus.arm_2.zip mp_litmus do
    println! prettyPrintLitmusResult test res

  println! "running ARM 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.arm_3
  for (test,res) in Litmus.arm_3.zip mp_litmus do
    println! prettyPrintLitmusResult test res
/-
  println! "running ARM 4-thread (IRIW) tests"
  let iriw_litmus := runMultipleLitmus Litmus.arm_4  (logProgress := true)
  for (test,res) in Litmus.arm_4.zip iriw_litmus do
    println! prettyPrintLitmusResult test res
-/
