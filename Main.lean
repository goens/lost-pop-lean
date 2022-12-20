import Cli

import Pop
import Pop.Arch

def interact : Cli.Parsed → IO UInt32
  | _ => do
    let some arch ← selectArchitecture (← IO.getStdin)
      | return 1
    let res ← @Pop.interactiveExecution (arch.getInstArch) (arch.getLitmusTests) (← IO.getStdin)
      if let .error msg  := res then
        println! msg
        return 0
      return 1

def interactCmd := `[Cli|
    interactCmd VIA interact;
    "Interactive mode."
    ]

def main (args : List String) : IO UInt32 :=
  interactCmd.validate args
