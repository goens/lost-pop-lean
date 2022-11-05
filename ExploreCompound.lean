import Pop
import Pop.Arch

open Pop Compound

def arch := ArchType.Compound
def allTests := arch.getLitmusTests
def tests_2 := allTests.filter λ lit => lit.numThreads == 2
def tests_3 := allTests.filter λ lit => lit.numThreads == 3
def tests_4 := allTests.filter λ lit => lit.numThreads == 4

def main : IO Unit := do

  println! "running Compound 2-thread tests"
  let mp_litmus := runMultipleLitmus tests_2
  println! printMultipleLitmusResults mp_litmus (printWitnesses := false)

  println! "running Compound 3-thread tests"
  let mp_litmus := runMultipleLitmus tests_3 (maxIterations := some 2000)
  println! printMultipleLitmusResults mp_litmus (printWitnesses := false)

  println! "running Compound 4-thread tests"
  let mp_litmus := runMultipleLitmus tests_4 (maxIterations := some 2000)
  println! printMultipleLitmusResults mp_litmus
