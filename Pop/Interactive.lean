import Pop.States
import Pop.Pop
import Pop.Program
import Pop.Exploration
import Pop.Litmus
import Pop.Util

/-
def examplemain : IO Unit := do
  let stdin ← IO.getStdin
  let inputLine ← stdin.getLine
  let kilos := inputLine.toNat!
  if kilos % 2 == 0 then
  IO.println "Yes"
  else
  IO.println "No"
-/

namespace Pop

def requestTransitionMessage : SystemState → ProgramState → Except String String
  | sysSt, progSt =>
    let available := sysSt.possibleTransitions progSt
    if available.isEmpty
    then
      Except.error "No transitions available!"
    else
      Except.ok $ String.intercalate "\n" $ List.range available.length
      |>.map (· + 1) |>.zip available |>.map λ (n,trans) => s!"{n}: {trans}"

def getTransition : SystemState → ProgramState → String → Except String (Option Transition)
  | sysState, progState, input => do
  let available := sysState.possibleTransitions progState
  let some n := input.toNat?
    | Except.error $ s!"Invalid input (must be a number from 0 to {available.length})"
     ++ s!"Received:{input}"
  if n == 0 then
    return none
  let some trans := available[n - 1]?
    | Except.error s!"Invalid index ({n}), must be between 1 and {available.length}"
  Except.ok $ some trans

def interactiveExecutionSingle : Litmus.Test → IO.FS.Stream → IO SearchState
  | ((initTrans,initProgSt),initSysSt), stdin => do
    let Except.ok start := initSysSt.applyTrace initTrans
      |  do IO.println s!"error initalizing litmus"; return ([],initProgSt,initSysSt)t
    let mut partialTrace := []
    let mut programState := initProgSt
    let mut finished := false
    while !finished do
      let systemState <- Util.exceptIO $ start.applyTrace partialTrace
      if finishedNoDeadlock systemState programState then
        finished := true
        break
      IO.println $ "------------------\n" ++ s!"Current state:\n{systemState}\n"
        ++ "Possible transitions:\n" ++ "0: Undo (last transition)"
      let exceptTransMsg  := requestTransitionMessage systemState programState
      if !exceptTransMsg.isOk then
        finished := true
      let msg := match exceptTransMsg with
        | Except.ok m => m
        | Except.error m => m
      IO.println msg
      let mut step := Except.error "Unknown transition"
      while !step.isOk do
        let input <- stdin.getLine
        step := getTransition systemState programState input.trim
      let opTransition := step.toOption.get!
      if let some transition := opTransition then
        partialTrace := partialTrace ++ [transition]
        programState := programState.removeTransition transition
      else
        if let some transition := partialTrace[partialTrace.length - 1]? then
          programState := programState.appendTransition transition
          partialTrace := partialTrace.dropLast
    let finalState <- Util.exceptIO $ start.applyTrace partialTrace
    return (partialTrace,programState,finalState)t

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

def interactiveExecution : List Litmus.Test → IO.FS.Stream → IO SearchState
  | tests, stdin => do
    let mut selected := Except.error "No litmus test selected"
    let litmusStrings :=  tests.map λ ((_,progState),_) => progState.prettyPrint
    let indices := List.range (litmusStrings.length) |>.map (· +1)
    let fullStrings := indices.zip litmusStrings |>.map λ (idx, lit) => s!"{idx}: {lit}"
    let availableString := String.intercalate "\n" fullStrings
    while !selected.isOk do
      IO.println s!"Select litmus test. Available:\n{availableString}"
      let input <- stdin.getLine
      selected := selectLitmus tests input
      if let Except.error msg := selected then
        IO.println s!"Error: {msg}"
    let litmus := selected.toOption.get!
    interactiveExecutionSingle litmus stdin

end Pop
