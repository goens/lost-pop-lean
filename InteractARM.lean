import Pop
import Pop.Arch.ARM
import Litmus.ARM

open Pop ARM

def main : IO Unit := do
let res ← Pop.interactiveExecution (Litmus.allARM) (← IO.getStdin)
  if let .error msg  := res then
    println! msg
