import Pop
import Pop.Arch.TSO
import Litmus.TSO

open Pop x86
open Litmus

#eval dekkers_fence.program
def main : IO Unit := do
  println! "running TSO 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_2
  println! printMultipleLitmusResults mp_litmus

  println! "running TSO 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_3 (maxIterations := some 100000)
  println! printMultipleLitmusResults mp_litmus

  println! "running TSO 4-thread tests"
  let mp_litmus := runMultipleLitmus [Litmus.IRIW] (maxIterations := some 100000)
  println! printMultipleLitmusResults mp_litmus (printWitnesses := true)
