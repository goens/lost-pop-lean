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
def getTransition : SystemState → ProgramState → String → Except String Transition
  | sysState, progState, input => do
  let available := sysState.possibleTransitions progState
  let some n := input.toNat?
    | Except.error $ s!"Invalid input (must be a number from 1 to {available.length})"
     ++ s!"Received:{input}"
  if n == 0 then
    throw s!"Invalid index (0), must be between 1 and {available.length}"
  let some trans := available[n - 1]?
    | Except.error s!"Invalid index ({n}), must be between 1 and {available.length}"
  Except.ok trans

def interactiveExecution : Litmus.Test → IO.FS.Stream → IO Outcome
  | ((initTrans,initProgSt),initSysSt), stdin => do
    let Except.ok start := initSysSt.applyTrace initTrans
      |  do IO.println s!"error initalizing litmus"; return []
    let mut systemState := start
    let mut programState := initProgSt
    let mut finished := false
    while !finished do
      IO.println $ s!"Current state:\n{systemState}\n"
        ++ "Possible transitions:\n"
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
      let transition := step.toOption.get!
      let exceptSystemState := systemState.applyTransition transition
      systemState <- Util.exceptIO exceptSystemState
      programState := programState.removeTransition transition
      if !exceptSystemState.isOk || finishedNoDeadlock systemState programState then
        finished := true
    return systemState.outcome
end Pop
