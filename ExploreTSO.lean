import Pop
import Pop.Arch.TSO
import Litmus.TSO

open Pop x86

def main : IO Unit := do
  println! "running TSO 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tso_2
  println! printMultipleLitmusResults mp_litmus

  println! "running TSO 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tso_3 (maxIterations := some 10000)
  println! printMultipleLitmusResults mp_litmus

  println! "running TSO 4-thread tests"
  let mp_litmus := runMultipleLitmus [Litmus.IRIW] (maxIterations := some 10000)
  println! printMultipleLitmusResults mp_litmus
