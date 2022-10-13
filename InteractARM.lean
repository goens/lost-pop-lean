import Pop
import Pop.Arch.ARM
import Litmus.ARM

open Pop ARM

def main : IO Unit := do
let res ← Pop.interactiveExecution (Litmus.allARM) (← IO.getStdin)
  if let .ok (trace,litmus,systemState)t := res
  then
    let outcome := systemState.partialOutcome
    println! "========================="
    println! "=======  SUMMARY  ======="
    println! "========================="
    println! s!"Litmus: {litmus.prettyPrint}\n" ++ s!"Trace: {trace}\n" ++ s!"Outcome: {outcome.prettyPrint}"
  if let .error msg  := res then
    println! msg
