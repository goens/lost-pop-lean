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

def parseLitmus :  (arch : ArchType) → Option Cli.Parsed.Flag → Except String (List $ @Litmus.Test arch.getInstArch)
  | arch, opLitmusArg => do
        let some litmusArg := opLitmusArg
          | .ok []
        let some litmusStr := litmusArg.as? (Array String)
          | .error "Error parsing flag"
        litmusStr.toList.mapM
          λ str => match arch.getLitmusTests.find?
            λ litmus => str == (@Litmus.Test.name arch.getInstArch litmus)
              with
               | none => .error s!"Unknown litmus test: {str}"
               | some test => .ok test

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
    let partialTrace := match args.flag? "partial-trace" with
      | none => []
      | some flag => flag.as! (Array Nat) |>.toList
    let litmus ← match parseLitmus arch (args.flag? "litmus") with
      | .ok [test] => pure test
      | .ok [] =>
        let exceptLitmus ← @Pop.selectLitmusLoop arch.getInstArch arch.getLitmusTests (← IO.getStdin)
        match exceptLitmus with
          | .ok test => pure test
          | .error msg  => IO.println msg; return 1
      | .ok _ => IO.println "selected multiple litmus tests for interactive mode, only 1 supported"; return 1
      | .error msg => IO.println msg; return 1
    let res ← @Pop.interactiveExecutionSingle (arch.getInstArch) litmus partialTrace (← IO.getStdin)
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
    -- TODO: guide trace?
    let tests ← if !(args.hasFlag "litmus") then
      pure $ arch.getLitmusTests.filter λ test => threads.contains (@Litmus.Test.numThreads arch.getInstArch test)
      else match parseLitmus arch (args.flag? "litmus") with
        | .ok tests => pure tests
        | .error msg => do
          IO.println msg; return 1
    let maxIterationsString := match maxIterations with
      | none => "unlimited iterations"
      | some max => s!"maximum {max} iterations"
    IO.println s!"Exploring {arch}: {tests.length} tests with {threads} threads, with batch size {batchSize}, {maxIterationsString}..."
    let litmusRes := @Pop.runMultipleLitmus arch.getInstArch tests
                                            (logProgress := false) (batchSize := batchSize) (maxIterations := maxIterations) (randomSeed := randomSeed)
    IO.println $ @Pop.printMultipleLitmusResults arch.getInstArch litmusRes (printWitnesses := args.hasFlag "print-witnesses")
    return 0

def alloy : Cli.Parsed → IO UInt32
  | args => do
    let some arch ← parseArchIO args
      | return 1
    let outputDir : System.FilePath := match args.flag? "output-dir" with
      | some dir => dir.as! String
      | none => "alloy_generated" / s!"{arch}/"
    let tests ← match parseLitmus arch (args.flag? "litmus") with
      | .ok [] => pure arch.getLitmusTests
      | .ok ts => pure ts
      | .error msg => IO.println msg; return 1
    IO.println s!"generating Alloy {tests.length} tests for {arch}"
    for litmus in tests do
       IO.FS.createDirAll outputDir
       let outputFile := outputDir / (@Litmus.Test.name arch.getInstArch litmus ++ ".als")
       IO.FS.writeFile outputFile $ @toAlloyLitmus arch.getInstArch arch.getInstLitmusSyntax litmus
    return 0


def selectMode : Cli.Parsed → IO UInt32
  | args => do
    if args.hasFlag "list-archs" then
      IO.println $ "Available architectures: " ++ (String.intercalate "\n" $ ArchType.available.map toString)
      return 0
    if args.hasFlag "explore" then
      explore args
    else if args.hasFlag "axiomatic-alloy" then
      alloy args
    else -- default: interact
      interact args

def mainCmd := `[Cli|
    pop VIA selectMode;
    "Execute litmus tests on the LOST-POP model."
    FLAGS:
      a, arch : String;                     "Select the target architecture"
      "list-archs";                         "List all available architectures"
      e, explore;                           "Automatically explore the litmus test(s). Default is interactive exploration"
      b, "batch-size" : Nat;                "Batch size for exploration"
      r, "random-seed" : Nat;               "Random seed for exploration"
      i, "iterations" : Nat;                "Maximum number of iterations (unlimited if not provided)"
      l, "litmus" : String;                 "Name of a specific litmus test"
      t, "filter-num-threads" : Array Nat;  "Print witnesses when exploring"
      p, "partial-trace" : Array Nat;       "Provide a partial (guide) to start the litmus test"
      w, "print-witnesses";                 "Print witnesses when exploring"
      A,"axiomatic-alloy";                  "Generate axomatic version of test in Alloy format"
      D,"output-dir" : String;              "Output directory"
    ]


def main (args : List String) : IO UInt32 :=
  mainCmd.validate args
