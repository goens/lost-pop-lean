import Pop
import Pop.Arch.PTX

open Pop PTX

def main : IO Unit := do
  println! "running PTX 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.ptx_2
  println! printMultipleLitmusResults mp_litmus (printWitnesses := false)

  println! "running PTX 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.ptx_3 (maxIterations := some 20000)
  println! printMultipleLitmusResults mp_litmus (printWitnesses := true)

/-
  println! "running PTX 4-thread (IRIW) tests"
  let mp_litmus := runMultipleLitmus Litmus.ptx_4
  println! printMultipleLitmusResults mp_litmus
-/
