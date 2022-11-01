import Pop
import Pop.Arch.Compound
import Litmus.Compound

open Pop Compound

def main : IO Unit := do
  println! "running Compound 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_2
  println! printMultipleLitmusResults mp_litmus (printWitnesses := false)

  println! "running Compound 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_3 (maxIterations := some 2000)
  println! printMultipleLitmusResults mp_litmus (printWitnesses := false)

  println! "running Compound 4-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_4 (maxIterations := some 2000)
  println! printMultipleLitmusResults mp_litmus
