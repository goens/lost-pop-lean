import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Std.Data
import Pop.Litmus
open Std.HashMap
open Util

namespace Pop

def ProgramState.prettyPrint : ProgramState → String
  | stArr => String.intercalate " || " <| Array.toList <|
     stArr.map λ thread =>
       String.intercalate "; " $ filterNones $ Array.toList <|
         thread.map Transition.prettyPrintReq

def ProgramState.getAvailable (prog : ProgramState) : List (Transition) := Id.run do
  let mut res := []
  for thread in prog do
    if h : thread.size > 0 then
    res := thread[0] :: res
  --dbg_trace "{prog.map λ tr => tr.map Transition.prettyPrintReq}.available = {res.map Transition.prettyPrintReq}"
  return res

def ProgramState.removeTransition (prog : ProgramState) (transition : Transition)
  : ProgramState := Id.run do
  let mut res := #[]
  let mut thread' := #[]
  for thread in prog do
    thread' := thread.erase transition
    res := res.push thread'
  return res

-- Should hold: remove · append = id
def ProgramState.appendTransition : ProgramState → Transition → ProgramState
  | prog, trans@(.acceptRequest _ thId) => Id.run do
  let mut res := #[]
  let mut thread' := #[]
  for idx in [:prog.size] do
    thread' := prog[idx]!
    if idx == thId then
      thread' := #[trans] ++ thread'
    res := res.push thread'
  return res
  | prog, _ => prog


def Request.possiblePropagateTransitions (req : Request) (state :  SystemState) : List (Transition) :=
  let threads := state.threads.removeAll req.propagated_to
  --dbg_trace s!"Req {req.id} has not propagated to {threads}"
  let threads_valid := threads.filter (state.canPropagate req.id)
  --dbg_trace s!"Req {req.id} can propagate to {threads_valid}"
  threads_valid.map λ th => Transition.propagateToThread req.id th

def SystemState.possiblePropagateTransitions (state :  SystemState) : List (Transition) :=
  let requests := filterNones state.requests.val.toList
  let requests_not_fully_propagated := requests.filter λ r => ! (@Request.fullyPropagated instArchReq state.scopes r state.scopes.systemScope)
  let removedIds := state.removed.map Request.id
  let requests_active := requests_not_fully_propagated.filter λ r => (state.seen.elem r.id) && (!removedIds.elem r.id)
  -- dbg_trace s!"active requests: {requests_active}"
  List.join $ requests_active.map λ r => r.possiblePropagateTransitions state

def Request.possibleSatisfyTransitions (read : Request) (state : SystemState) : List (Transition) :=
  if !read.isRead then [] else
    let requests := filterNones state.requests.val.toList
    let writes_propagated_eq := requests.filter λ write => write.isWrite && write.propagated_to == read.propagated_to
    --dbg_trace s!"writes with eq propagation to {read.id}: {writes_propagated_eq}"
    let write_ids := writes_propagated_eq.map Request.id
    let writes_valid := write_ids.filter (λ write => state.canSatisfyRead read.id write) -- should be length 1
    --dbg_trace s!"valid writes for transition: {writes_valid}"
    writes_valid.map $ Transition.satisfyRead read.id

def SystemState.possibleSatisfyTransitions (state :  SystemState) : List (Transition) :=
  let requests := filterNones state.requests.val.toList
  let unsatisfied_reads := requests.filter λ r => r.isRead && !(state.isSatisfied r.id)
  List.join $ unsatisfied_reads.map λ r => r.possibleSatisfyTransitions state

def SystemState.possibleTransitions (state : SystemState) (unaccepted : ProgramState) :=
  let allaccepts := unaccepted.map λ th => th.filter Transition.isAccept
  let accepts := ProgramState.getAvailable allaccepts
  accepts ++ state.possibleSatisfyTransitions ++ state.possiblePropagateTransitions

def SystemState.hasUnsatisfiedReads (state : SystemState) :=
  let requests := filterNones state.requests.val.toList
  let reads := requests.filter Request.isRead
  let readids := reads.map Request.id
  let unsatisfied := readids.filter state.isSatisfied
  unsatisfied != []

def SystemState.isDeadlocked (state : SystemState) (unaccepted : ProgramState) :=
  let transitions := state.possibleTransitions unaccepted
  transitions == [] && state.hasUnsatisfiedReads

-- This should be a monad transformer or smth...
def SystemState.takeNthStep (state : SystemState) (acceptRequests : ProgramState)
(n : Nat) : Except String (Transition × SystemState) :=
  let transitions := state.possibleTransitions acceptRequests
  --dbg_trace s!"possible transitions: {transitions}"
  if transitions.isEmpty then
    throw "No more transitions possible"
  else
    let opTrans := transitions.get? (n.mod transitions.length)
    match opTrans with
      | none => unreachable!
      | some trans => Except.map (λ st => (trans, st)) (state.applyTransition trans)

def SystemState._runWithList  : SystemState →  ProgramState → List Nat → Except String (SystemState)
  | state, accepts, ns => match ns with
    | [] => throw "Empty transition number list"
    | n::ns =>
      let runStep := state.takeNthStep accepts n
      match runStep with
        | Except.error "No more transitions possible" => Except.ok state
        | Except.ok (trans,state') =>
          -- dbg_trace trans.toString
          -- dbg_trace state'
          state'._runWithList (ProgramState.removeTransition accepts trans) ns
        | Except.error e => Except.error e

def SystemState.runWithList  : SystemState →  ProgramState → List Nat → Except String (SystemState)
  | state, accepts, ns => if !(List.join (accepts.map Array.toList).toList |>.all Transition.isAccept)
  then throw "Running with non-accept transition inputs"
  else SystemState._runWithList state accepts ns


/-
private def appendTransitionStateAux : List (List Transition × SystemState) → Transition × SystemState  → List (List Transition × SystemState)
  | partialTrace, (trans,state) => partialTrace.map λ (transitions, _) => (trans::transitions, state)

Stack overflow :

-- is this DFS or BFS?
partial def SystemState.runDFSAux (state : SystemState) (accepts : List Transition) (condition : SystemState → Bool)
  (partialTrace : List (List Transition × SystemState)) (transition : Transition): List (List Transition × SystemState) :=
  --dbg_trace s!"partialTrace {partialTrace.map fun (t,_) => t}"
  --dbg_trace s!"executing {transition}"
  let accepts' := accepts.removeAll [transition]
  let stepExcept := state.applyTransition transition
  match stepExcept with
    | Except.error _ => []
    | Except.ok state' =>
      let partialTrace' := appendTransitionStateAux partialTrace (transition,state')
      if condition state'
      then partialTrace'
      else if state'.isDeadlocked accepts'
      then []
      else
        let transitions' := state'.possibleTransitions accepts'
        List.join $ transitions'.map (state'.runDFSAux accepts' condition partialTrace')

def SystemState.runDFS : SystemState → List Transition × List Transition → (SystemState → Bool) →
  List (List Transition × SystemState)
  | state, (inittransitions, accepts), condition =>
  let stateinit := state.applyTrace inittransitions
  match stateinit with
    | .ok st =>
      let transitions := st.possibleTransitions accepts
      List.join $ transitions.map (st.runDFSAux accepts condition [([],state)])
    | .error _ =>
      --dbg_trace s!"error: {e}"
      [(inittransitions,state)]
-/

abbrev SearchState := Triple (List Transition) ProgramState SystemState

private def searchAuxStep (stopAtCondition : Bool) (storePartialTraces : Bool)
(condition : SystemState → ProgramState → Bool)
(partialTrace : List Transition) (acceptsRemaining : ProgramState) (st : SystemState)
: Array SearchState :=
  let transitions := st.possibleTransitions acceptsRemaining
  --let debug := if true--transitions.length == 0
  --  then s!"requests:\n{st.requests}\n available:\n{transitions}\n------"
  --  else ""
  --dbg_trace debug
  if stopAtCondition && condition st acceptsRemaining
  then Array.mk []
  else
    transitions.toArray.map λ t =>
      let newPT := (if storePartialTraces
                    then partialTrace ++ [t]
                    else [])
    -- TODO: this could yield a bug if we have two identical requests in a litmus test
      let newAC :=       ProgramState.removeTransition acceptsRemaining t
      -- dbg_trace "{acceptsRemaining.prettyPrint}, removing {t.prettyPrintReq}, yields: {newAC.prettyPrint}"
      -- TODO: add potential to sanity check
      let newST := st.applyTransition! t
      (newPT,newAC,newST)t

private def searchAuxUpdateUnexplored (explored unexplored newtriples : Array SearchState) : Array SearchState :=
  let filterFun := λ (_,newProgState,newSysState)t =>
    let checkFun := λ (_,progState,sysState)t =>
      newProgState != progState || newSysState != sysState
    (unexplored.all checkFun && explored.all checkFun)
  Array.append (newtriples.filter filterFun) unexplored

private def searchAuxCheckCondition
(condition : SystemState → ProgramState → Bool) (newTriples : Array SearchState)
: List (List Transition × SystemState) :=
  filterNones $ newTriples.toList.map λ triple =>
    if condition triple.3 triple.2
      then some (triple.1,triple.3)
      else none

private def searchAuxNSteps (stopAtCondition : Bool) (storePartialTraces : Bool)
  (condition : SystemState → ProgramState → Bool) (n : Nat) (inputStates : Array SearchState)
 : List (List Transition × SystemState) × Array SearchState := Id.run do
 let mut unexplored := inputStates
 let mut stepsRemaining := n
 let stepFun := searchAuxStep stopAtCondition storePartialTraces condition
 while h : unexplored.size > 0 && stepsRemaining > 0 do
   let (partialTrace,acceptsRemaining,st)t := unexplored[unexplored.size - 1]'
     (by rw [Bool.and_eq_true] at h
         let h' := of_decide_eq_true $ And.left h
         exact n_minus_one_le_n h')
   let newTriples := stepFun partialTrace acceptsRemaining st
   unexplored := unexplored.pop
   unexplored := searchAuxUpdateUnexplored #[] unexplored newTriples
   --dbg_trace "popped {partialTrace}, remaining unexplored{unexplored.map λ (pt,_,_)t => pt} "
   stepsRemaining := stepsRemaining - 1
 let found := searchAuxCheckCondition condition unexplored
 --dbg_trace "returning unexplored: {unexplored.map λ triple => triple.1}"
 (found,unexplored)

-- the unapologetically imperative version:
def SystemState.runSearch (state : SystemState) (inittuple : List (Transition) × ProgramState)
 (condition : SystemState → ProgramState → Bool) (stopAtCondition : optParam Bool false)
 (storePartialTraces : optParam Bool false) (numWorkers : optParam Nat 7)
 (batchSize : optParam Nat 15) (breadthFirst : optParam Bool false)
 (logProgress : optParam Bool false) :
 List (List (Transition) × SystemState) :=
match inittuple with
  | (inittransitions, accepts) =>
  let stateinit := state.applyTrace inittransitions
  let stepFun := searchAuxNSteps stopAtCondition storePartialTraces condition batchSize
  match stateinit with
    | .ok startState =>
    Id.run do
      -- either save the state (memory cost) or recompute it (computational cost)
      -- we choose the former so that we can also filter out states that we've seen before
      let mut unexplored := #[([],accepts,startState)t]
      let mut explored := #[]
      let mut found := []
      let mut cur_size := 0
      let mut thousands_explored : UInt32 := 1
      --dbg_trace s!"litmus: {accepts.prettyPrint}"
      --dbg_trace s!"starting state:\n{startState}"
      let mut workers : Array (Task (List (List Transition × SystemState) × Array SearchState)) := #[]
      while unexplored.size > 0 do
          --dbg_trace s!"{unexplored.size} unexplored"
          let n := min unexplored.size (max numWorkers 1) -- at least 1
          for i in [0:n] do
            -- FIXME: Change cur! (??)
            -- BFS : first
            --let some unexplored_cur := unexplored[i]?
            let idx := if breadthFirst then unexplored.size - 1 else i
            let some unexplored_cur := unexplored[idx]?
              | panic! "index error, this shouldn't happen" -- TODO: prove i is fine
            unexplored := unexplored.eraseIdx idx
            if !breadthFirst then
              explored := explored.push unexplored_cur
            let task := Task.spawn λ _ => stepFun #[unexplored_cur]
            workers := workers.push task
          for worker in workers do
            let (newFound,newTriples) := worker.get
            found := newFound ++ found
            if logProgress then
              if newTriples.any λ (pt,_,_)t => pt.length > cur_size then
                cur_size := cur_size + 1
                dbg_trace "progress: partial traces of size {cur_size}"
              if explored.size.toUInt32 > thousands_explored  * 1000 then
                dbg_trace "progress: explored ≥{thousands_explored}k"
                thousands_explored := thousands_explored + 1

            unexplored := searchAuxUpdateUnexplored explored unexplored newTriples
            --dbg_trace "total unexplored: {unexplored.size}"
          workers := #[]
      return found
    | .error _ => -- TODO: make this function also an Except value
    [(inittransitions,state)]

def finishedNoDeadlock (state : SystemState) (unaccepted : ProgramState) : Bool :=
  let transitions := state.possibleTransitions unaccepted
  transitions == [] && !state.hasUnsatisfiedReads

def SystemState.runSearchNoDeadlock
  (state : SystemState) (litmus : List (Transition) × ProgramState)
  (stopAtCondition : optParam Bool false)
  (storePartialTraces : optParam Bool true) (numWorkers : optParam Nat 7)
  (batchSize : optParam Nat 15) (breadthFirst : optParam Bool false)
  (logProgress : optParam Bool false):
  List (List (Transition) × SystemState) :=
    let reads : Array (Array Nat) := litmus.2.map
      λ thread => thread.map
        λ tr => if tr.isReadAccept then 1 else 0
    let numReads : Nat := Array.sum $ reads.map λ th => Array.sum th
      let finishedFun := λ sysSt prSt =>
        let transitions := sysSt.possibleTransitions prSt
        -- dbg_trace "{sysSt.satisfied.length}/{numReads}"
        transitions == [] && sysSt.satisfied.length == numReads
    state.runSearch litmus finishedFun stopAtCondition storePartialTraces numWorkers
      batchSize breadthFirst logProgress

-- Doesn't work. Need to combine removed with requests
-- def SystemState.satisfiedRequestPairs : SystemState → List (Request × Request)
--   | state =>
--     let pairsOpt := state.satisfied.map λ (rdId, wrId) => (state.requests.val[rdId], state.requests.val[wrId])
--     let optPairs := pairsOpt.map λ (opRd, opWr) => match (opRd,opWr) with
--       | (some rd, some wr) => some (rd,wr)
--       | _ => none
--     filterNones optPairs

abbrev Outcome := List $ ThreadId × Address × Value

def SystemState.outcome : SystemState → Outcome
  | state =>
    -- TODO: this won't work for reads that stay there
    let triple := state.removed.map λ rd => (rd.thread, rd.address?.get!, rd.value?)
    triple.toArray.qsort (λ (th,ad,_) (th',ad',_) => lexBLe (th,ad) (th',ad')) |>.toList

def addressValuePretty : Address × Value → String
  | (_, none) => "invalid outcome!"
  | (addr, some val) => s!"{addr.prettyPrint} = {val}"

def Outcome.prettyPrint : Outcome → String
  | outcome =>
  let threads : List Outcome := outcome.groupBy (·.1 == ·.1)
  let threadStrings := threads.map
    λ th => String.intercalate "; " $ th.map (addressValuePretty $ Prod.snd ·)
  String.intercalate " || " threadStrings

def runMultipleLitmus : List Litmus.Test → List (List Outcome)
  | tests =>
  Id.run do
    let mut tasks : Array (Task (List Outcome)) := #[]
    for test in tests do
      let task := Task.spawn λ _ =>
        let resExpl := test.2.runSearchNoDeadlock test.1
        let resLitmus := Util.removeDuplicates $ resExpl.map λ (_,st) => st.outcome
        resLitmus
      tasks := tasks.push task
    return tasks.map Task.get  |>.toList

def prettyPrintLitmusResult : Litmus.Test → List Outcome → String
  | test, reslit =>
     let outcomes_pretty := String.intercalate "\n" $
       reslit.map λ outcome => outcome.prettyPrint
     let litStr := ProgramState.prettyPrint test.1.2
     s!"litmus:{litStr}\n" ++ s!"outcomes:\n{outcomes_pretty}"
/-
  Id.run do
    let mut res := ""
    let mut curThread : ThreadId := 0
    for (thread, addr, opval) in outcome do
      while (ThreadId.toNat curThread ) < (ThreadId.toNat thread) do
        -- assumes lexBLe, won't add multiple ||'s
        res := res ++ "|| "
        curThread := (ThreadId.toNat curThread) + 1
      let some val := opval then
        res := res ++ s!"x{addr} := {val}; "
      else
        res := "invalid outcome!"
        break
    return res
    -/
-- | state, accepts => state.runDFS accepts λ _ => false

    -- let runStep := λ (acceptsRemaining, state) n => state.takeNthStep acceptsRemaining n
    -- ns.foldlM (init := (accepts, state)) runStep
    -- ns.foldlM  (init := state) λ state.takeNthStep accepts.zip ns
