import Pop.States
import Pop.Pop
import Pop.Exploration
import Pop.Litmus
import Pop.Util

namespace Pop

variable [Arch]

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
        let msg := "======================================\n"
          ++ s!"{name}, program state:\n{programState.prettyPrint}\n"
          ++ s!"scopes : {systemState.scopes.toStringHet (some systemState.threadTypes)}\n"
          ++ "--------------------------------------\n"
          ++ s!"Current trace:\n{partialTraceNums}\n"
          ++ "--------------------------------------\n"
          ++ s!"Current state:\n{systemState}\n"
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

end Pop
