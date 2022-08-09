import Pop
open Pop

def main : IO Unit := do
  let (trace,litmus,systemState)t <- Pop.interactiveExecution (Litmus.x86_2 ++ Litmus.x86_4) (← IO.getStdin)
  let outcome := systemState.outcome
  println! "========================="
  println! "=======  SUMMARY  ======="
  println! "========================="
  println! s!"Litmus: {litmus.prettyPrint}\n" ++ s!"Trace: {trace}\n" ++ s!"Outcome: {outcome.prettyPrint}"
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

