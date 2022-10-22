import Pop
import Pop.Arch.TSO
import Litmus.TSO

open Pop x86

def main : IO Unit := do
let res ← Pop.interactiveExecution (Litmus.allTSO) (← IO.getStdin)
  if let .error msg  := res then
    println! msg
