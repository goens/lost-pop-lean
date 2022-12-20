import Cli

import Pop
import Pop.Arch

def parseArch : Option Cli.Parsed.Flag → Except String ArchType
  | opArchArg => do
        let some archArg := opArchArg
          | .error "Error parsing flag"
        let some arch := archArg.as? String
          | .error "Error parsing flag"
        parseArchitectureString arch

def interact : Cli.Parsed → IO UInt32
  | args => do
    let some arch ←
      if args.hasFlag "arch" then
        do
          let archRes := parseArch $ args.flag? "arch"
          match archRes with
            | Except.ok arch => (return some arch)
            | Except.error msg => do
              IO.println msg; (return none)
      else
          selectArchitecture (← IO.getStdin)
      |  return 1
    let res ← @Pop.interactiveExecution (arch.getInstArch) (arch.getLitmusTests) (← IO.getStdin)
      if let .error msg  := res then
        println! msg
        return 0
      return 1

def mainCmd := `[Cli|
    mainCmd VIA interact;
    "Defaults to interactive mode."
    FLAGS:
      a, arch : String;      "Select the target architecture"
      "list-archs";    "List all available architectures"
    ]


def main (args : List String) : IO UInt32 :=
  mainCmd.validate args
