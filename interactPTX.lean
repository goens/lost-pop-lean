import Pop
import Pop.Arch.PTX
import Litmus.PTX

open Pop PTX

def main : IO Unit := do
/-
  replayNumTrace Litmus.WWRWRR [2, 3, 2, 5, 2, 1, 5, 1, 4, 2, 2, 2, 3, 2, 1, 1, 2, 3, 3, 2, 1] (← IO.getStdin)
-/

let res ← Pop.interactiveExecution (Litmus.allPTX) (← IO.getStdin)
  if let .ok (trace,litmus,systemState)t := res
  then
    let outcome := systemState.partialOutcome
    println! "========================="
    println! "=======  SUMMARY  ======="
    println! "========================="
    println! s!"Litmus: {litmus.prettyPrint}\n" ++ s!"Trace: {trace}\n" ++ s!"Outcome: {outcome.prettyPrint}"
  if let .error msg  := res then
    println! msg
