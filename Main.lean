import Pop
open Pop

def main : IO Unit := do
  let outcome <- Pop.interactiveExecution (Litmus.IRIW, Litmus.inittso_4) (← IO.getStdin)
  println! "Outcome: {outcome.prettyPrint}"
  /-
  println! "running TSO MP tests"
  let mp_litmus := runMultipleLitmus Litmus.x86_2
  for (test,res) in Litmus.x86_2.zip mp_litmus do
    println! prettyPrintLitmusResult test res
  println! "running TSO IRIW tests"
  let iriw_litmus := runMultipleLitmus Litmus.x86_4
  for (test,res) in Litmus.x86_4.zip iriw_litmus do
    println! prettyPrintLitmusResult test res
  -/

