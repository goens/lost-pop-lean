import Pop
import Pop.Arch

def main : IO Unit := do
  let some arch ← selectArchitecture (← IO.getStdin)
    | return ()
  let res ← @Pop.interactiveExecution (arch.getInstArch) (arch.getLitmusTests) (← IO.getStdin)
    if let .error msg  := res then
      println! msg
