import Pop
import Pop.Arch.PTX
import Litmus.PTX

open Pop PTX

def main : IO Unit := do

let res ← Pop.interactiveExecution (Litmus.allPTX) (← IO.getStdin)
  if let .error msg  := res then
    println! msg
