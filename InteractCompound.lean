import Pop
import Pop.Arch.Compound
import Litmus.Compound

def main : IO Unit := do

let res ← Pop.interactiveExecution (Litmus.allCompound) (← IO.getStdin)
  if let .error msg  := res then
    println! msg
