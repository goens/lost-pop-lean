import Pop
import Pop.Arch.TSO

open Pop x86

def main : IO Unit := do
  println! "running TSO 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tso_2
  println! printMultipleLitmusResults mp_litmus (printWitnesses := false)

  println! "running TSO 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tso_3 (maxIterations := some 10000)
  println! printMultipleLitmusResults mp_litmus

/-
  println! "running TSO IRIW tests"
  let iriw_litmus := runMultipleLitmus Litmus.x86_4
  for (test,res) in Litmus.x86_4.zip iriw_litmus do
    println! prettyPrintLitmusResult test res
-/
