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

def parseArchIO : Cli.Parsed → IO (Option ArchType)
  | args => do
      if args.hasFlag "arch" then
        do
          let archRes := parseArch $ args.flag? "arch"
          match archRes with
            | Except.ok arch => (return some arch)
            | Except.error msg => do
              IO.println msg; (return none)
      else
          selectArchitecture (← IO.getStdin)

def interact : Cli.Parsed → IO UInt32
  | args => do
    let some arch ← parseArchIO args
      | return 1
    let res ← @Pop.interactiveExecution (arch.getInstArch) (arch.getLitmusTests) (← IO.getStdin)
      if let .error msg  := res then
        println! msg
        return 0
      return 1

def explore : Cli.Parsed → IO UInt32
  | args => do
    let some arch ← parseArchIO args
      | return 1
    let batchSize := match args.flag? "batch-size" with
      | some size => size.as! Nat
      | none => 6
    let maxIterations := match args.flag? "iterations" with
      | some iters => some $ iters.as! Nat
      | none => none
    let randomSeed := match args.flag? "random-seed" with
      | some seed => some $ seed.as! Nat
      | none => none
    let threads := match args.flag? "filter-num-threads" with
      | some ts => ts.as! (Array Nat) |>.toList
      | none => Util.removeDuplicates $ arch.getLitmusTests.map (@Litmus.Test.numThreads arch.getInstArch)
    let tests := arch.getLitmusTests.filter λ test => threads.contains (@Litmus.Test.numThreads arch.getInstArch test)
    let maxIterationsString := match maxIterations with
      | none => "unlimited iterations"
      | some max => s!"maximum {max} iterations"
    IO.println s!"Exploring {arch}: {tests.length} tests with {threads} threads, with batch size {batchSize}, {maxIterationsString}..."
    let litmusRes := @Pop.runMultipleLitmus arch.getInstArch tests
                                            (logProgress := false) (batchSize := batchSize) (maxIterations := maxIterations) (randomSeed := randomSeed)
    IO.println $ @Pop.printMultipleLitmusResults arch.getInstArch litmusRes (printWitnesses := args.hasFlag "print-witnesses")
    return 0

def selectMode : Cli.Parsed → IO UInt32
  | args => do
    if args.hasFlag "list-archs" then
      IO.println $ "Available architectures: " ++ (String.intercalate "\n" $ ArchType.available.map toString)
      return 0
    if args.hasFlag "explore" then
      explore args
    else -- default: interact
      interact args

def mainCmd := `[Cli|
    pop VIA selectMode;
    "Defaults to interactive mode."
    FLAGS:
      a, arch : String;                     "Select the target architecture"
      "list-archs";                         "List all available architectures"
      e, explore;                           "Automatically explore the architecture"
      b, "batch-size" : Nat;                "Batch size for exploration"
      r, "random-seed" : Nat;               "Random seed for exploration"
      i, "iterations" : Nat;                "Maximum number of iterations (unlimted if not provided)"
      t, "filter-num-threads" : Array Nat;  "Print witnesses when exploring"
    ]


def main (args : List String) : IO UInt32 :=
  mainCmd.validate args
