import Pop.States
import Pop.Pop
import Pop.Exploration
import Pop.Litmus
import Pop.Util

namespace Pop

variable [Arch]

inductive Key
  | up : Key
  | down : Key
  | left : Key
  | right : Key

def Key.toNat : Key → Nat
  | up => 72
  | down => 80
  | left => 75
  | right => 77

def Key.fromNat : Nat → Option Key
  | 72 => some up
  | 80 => some down
  | 75 => some left
  | 77 => some right
  | _ => none

def requestTransitionMessage : SystemState → ProgramState → Except String String
  | sysSt, progSt =>
    let available := sysSt.possibleTransitions progSt
    if available.isEmpty
    then
      Except.error "No transitions available!"
    else
      Except.ok $ String.intercalate "\n" $ List.range available.length
      |>.map (· + 1) |>.zip available |>.map
        λ (n,trans) => s!"{n}: {trans.prettyPrint sysSt}"

def getTransition : SystemState → ProgramState → String → Except String (Option (Transition × Nat))
  | sysState, progState, input => do
  let available := sysState.possibleTransitions progState
  let some n := input.trim.toNat?
    | Except.error $ s!"Invalid input (must be a number from 0 to {available.length})"
     ++ s!"Received:{input}"
  if n == 0 then
    return none
  let some trans := available[n - 1]?
    | Except.error s!"Invalid index ({n}), must be between 1 and {available.length}"
  Except.ok $ some (trans, n)

def formatInteractiveState (name : String) (programState : ProgramState) (systemState : SystemState) : String :=
          "======================================\n"
          ++ s!"{name}, program state:\n{programState.prettyPrint}\n"
          ++ s!"scopes : {systemState.scopes.toStringHet (some systemState.threadTypes)}\n"
          ++ "--------------------------------------\n"
          ++ s!"Current state:\n{systemState}\n"
          ++ "--------------------------------------\n"

def interactiveExecutionSingle : Litmus.Test → IO.FS.Stream → IO (Except String SearchState)
  | (.mk initTrans initProgSt _ initSysSt name _), stdin => do
    let Except.ok start := initSysSt.applyTrace initTrans
      |  do return Except.error "error initalizing litmus"
    let mut partialTrace := []
    let mut partialTraceNums := []
    let mut programState := initProgSt
    let mut finished := false
    while !finished do
      let systemState <- Util.exceptIO $ start.applyTrace partialTrace
      if systemState.finishedNoDeadlock programState then
        finished := true
        break
      let exceptTransMsg  := requestTransitionMessage systemState programState
      if let .error msg := exceptTransMsg  then
        return .error msg
      else if let .ok m := exceptTransMsg then
        let msg := formatInteractiveState name programState systemState
          ++ s!"Current trace:\n{partialTraceNums}\n"
          ++ "--------------------------------------\n"
          ++ "Possible transitions:\n" ++ "0: Undo (last transition)\n" ++ m
        let opStep ← Util.selectLoop msg (getTransition systemState programState) stdin
        if let some opTransition := opStep then
          if let some (transition, n) := opTransition then
            partialTrace := partialTrace ++ [transition]
            partialTraceNums := partialTraceNums ++ [n]
            programState := programState.consumeTransition systemState transition
              |>.clearDependencies (systemState.applyTransition! transition)
          else
            if let some transition := partialTrace[partialTrace.length - 1]? then
              programState := programState.appendTransition transition
              partialTrace := partialTrace.dropLast
              partialTraceNums := partialTraceNums.dropLast
        else
          finished := true
          return Except.error "^D"
    let finalState <- Util.exceptIO $ start.applyTrace partialTrace
    -- return initial program state (litmus) instead of finished
    return Except.ok (partialTrace,initProgSt,finalState)t

def selectLitmus :  List Litmus.Test → String → Except String Litmus.Test
| tests, input => do
  let some n := input.trim.toNat?
    | Except.error $ s!"Invalid input (must be a number from 1 to {tests.length})"
      ++ s!"Received:{input}"
  if n == 0 then
    Except.error s!"Invalid index ({n}), must be between 1 and {tests.length}"
  let some test := tests[n - 1]?
    | Except.error s!"Invalid index ({n}), must be between 1 and {tests.length}"
  Except.ok test

def selectLitmusLoop : List Litmus.Test → IO.FS.Stream → IO (Except String Litmus.Test)
  | tests, stdin => do
    let litmusStrings :=  tests.map λ test =>
      s!"{test.name} : " ++ test.program.prettyPrint ++
      (if test.initState.scopes.isUnscoped then ""
      else s!"\n  where sys := {test.initState.scopes.scopes}")
    let indices := List.range (litmusStrings.length) |>.map (· +1)
    let fullStrings := indices.zip litmusStrings |>.map λ (idx, lit) => s!"{idx}: {lit}"
    let availableString := String.intercalate "\n" fullStrings
    let opLitmus ← Util.selectLoop
      s!"Select litmus test. Available:\n{availableString}" (selectLitmus tests) stdin
    if let some litmus := opLitmus then
      return Except.ok litmus
    else
      return Except.error "^D"

def interactiveExecution : List Litmus.Test → IO.FS.Stream → IO (Except String SearchState)
  | tests, stdin => do
    let exceptLitmus ← selectLitmusLoop tests stdin
    match exceptLitmus with
      | .ok litmus => interactiveExecutionSingle litmus stdin
      | .error msg  => return Except.error msg

def replayTrace : Litmus.Test → List Transition → IO.FS.Stream → IO Unit
  | test, transitions@(_::_), stdin => do
    let initState ← Util.exceptIO $ test.initState.applyTrace test.initTransitions
    let mut ahead := transitions
    let mut behind := []
    while true do
      let programState ← Util.exceptIO $ test.program.consumeTrace initState behind
      let curState ← Util.exceptIO $ initState.applyTrace behind
      IO.println $ formatInteractiveState test.name programState curState
      IO.println $ s!"Executed so far: {behind}\n--------------------------------------"
      IO.println $ s!"Next: {ahead}\n--------------------------------------"
      let input := (← stdin.getLine).trim
      if input == "b" then
        dbg_trace "going backward"
        match behind with
          | [] => continue
          | beh =>
            ahead := beh.last'.get!::ahead
            behind := beh.reverse.tail.reverse
      if input == "f" then
        dbg_trace "going forward"
        match ahead with
          | [] => continue
          | next::rest =>
            behind := behind ++ [next]
            ahead := rest
      if input == "q" then
        break

  | _, [], _ => IO.println "Empty transition list"

def replayNumTrace : Litmus.Test → List Nat → IO.FS.Stream → IO Unit
  | test, transitions, stdin => match buildTransitionTrace test transitions with
     | none => IO.println "unable to convert numeric trace into litmus test trace"
     | some trace => replayTrace test trace stdin

end Pop
