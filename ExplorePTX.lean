import Pop
import Pop.Arch.PTX

open Pop PTX

def main : IO Unit := do
  println! "running PTX 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.ptx_2
  println! printMultipleLitmusResults mp_litmus

  println! "running PTX 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.ptx_3
  println! printMultipleLitmusResults mp_litmus

/-
  println! "running PTX 4-thread (IRIW) tests"
  let iriw_litmus := runMultipleLitmus Litmus.ptx_4  (logProgress := true)
  for (test,res) in Litmus.ptx_4.zip iriw_litmus do
    println! prettyPrintLitmusResult test res
-/
