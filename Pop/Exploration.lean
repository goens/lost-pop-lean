import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Pop.Litmus
open Std.HashMap
open Util

namespace Pop

variable [Arch]

def ProgramState.prettyPrint (accepts : ProgramState) : String :=
  let threadStrings := accepts.map λ th => filterNones $
    th.toList.map Transition.prettyPrintReq
  let allThreads := threadStrings.map λ th => String.intercalate "; " th
  String.intercalate " || " allThreads.toList

def ProgramState.getAvailable (prog : ProgramState) : List (Transition) := Id.run do
  let mut res := []
  for thread in prog do
    if h : thread.size > 0 then
      res := thread[0] :: res
  --dbg_trace "{prog.map λ tr => tr.map Transition.prettyPrintReq}.available = {res.map Transition.prettyPrintReq}"
  return res

def ProgramState.clearDependencies (prog : ProgramState) (state : SystemState)
  : ProgramState := Id.run do
  let mut res := #[]
  let mut thread' := #[]
  for thread in prog do
      thread' := thread
      if let some (Transition.dependency (some req)) := thread[0]? then
        if state.isSatisfied req then
          thread' := thread'.reverse.pop.reverse -- TODO: remove reverses?
      res := res.push thread'
  return res

def ProgramState.consumeTransition (prog : ProgramState) (state : SystemState) (transition : Transition)
  : ProgramState := Id.run do
  unless transition.isAccept do
    return prog
  let mut res : ProgramState := #[]
  let mut thread' := #[]
  let mut found := false -- just consume once
  for thread in prog do
    thread' := thread
    if !found then
      if let some transition' := thread[0]? then
        if transition' == transition then
          thread' := thread'.reverse.pop.reverse -- TODO: somehow don't reverse twice?
          found := true
          -- update dependency
          if let some (Transition.dependency none) := thread'[0]? then
            thread' := thread'.reverse.pop
            thread' := thread'.push (Transition.dependency state.freshId)
                |>.reverse -- TODO: somehow don't reverse twice here either?
    res := res.push thread'
  if found then return res
  else panic! s!"trying to consume non-existing transition: {transition}"

-- Should hold: remove · append = id
def ProgramState.appendTransition : ProgramState → Transition → ProgramState
  | prog, trans@(.acceptRequest _ thId) => Id.run do
  let mut res := #[]
  let mut thread' := #[]
  for idx in [:prog.size] do
    thread' := prog[idx]!
    if idx == thId then
      if let some (Transition.dependency (some _)) := thread'[0]? then
        thread' := thread'.reverse.pop -- TODO: another double reverse
        thread' := thread'.push (Transition.dependency none) |>.reverse
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
  let allaccepts := unaccepted.map λ th => th.filter (λ tr => tr.isAccept || tr.isDependency)
  let accepts := ProgramState.getAvailable allaccepts |>.filter state.canApplyTransition
  accepts ++ state.possibleSatisfyTransitions ++ state.possiblePropagateTransitions

def SystemState.hasUnsatisfiedReads (state : SystemState) :=
  let reads := state.requests.filter Request.isRead |>.map Request.id
  let unsatisfied := reads.filter λ r => !(state.isSatisfied r)
  unsatisfied != []

def SystemState.isDeadlocked (state : SystemState) (unaccepted : ProgramState) :=
  let transitions := state.possibleTransitions unaccepted
  transitions == [] && state.hasUnsatisfiedReads

def SystemState.outcome : SystemState → Litmus.Outcome
| state =>
  let removed := state.removed.map λ rd => (rd.thread, rd.address?.get!, rd.value?)
  let satisfied := state.requests.filter Request.isSatisfied
     |>.map λ rd => (rd.thread, rd.address?.get!, rd.value?)
  let triples := removed.toArray ++ satisfied.toArray
  triples.qsort (λ (th,ad,_) (th',ad',_) => lexBLe (th,ad) (th',ad')) |>.toList

def outcomeSubset : Litmus.Outcome → Litmus.Outcome → Bool
  | out₁, out₂ =>
  out₁.all λ triple => out₂.contains triple

def outcomeEqiv : Litmus.Outcome → Litmus.Outcome → Bool
  | out₁, out₂ => outcomeSubset out₁ out₂ && outcomeSubset out₂ out₁

def SystemState.outcomePossible : SystemState → Litmus.Outcome → Bool
 | state, expectedOutcome => outcomeSubset state.outcome expectedOutcome

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
          let newSt := accepts.consumeTransition state trans |>.clearDependencies state'
          state'._runWithList newSt ns
        | Except.error e => Except.error e

def SystemState.runWithList  : SystemState →  ProgramState → List Nat → Except String (SystemState)
  | state, accepts, ns => if !(List.join (accepts.map Array.toList).toList |>.all Transition.isAccept)
  then throw "Running with non-accept transition inputs"
  else SystemState._runWithList state accepts ns

def SystemState.finishedNoDeadlock (state : SystemState) (unaccepted : ProgramState) : Bool :=
  let transitions := state.possibleTransitions unaccepted
  transitions == [] && !state.hasUnsatisfiedReads


abbrev SearchState := Triple (List Transition) ProgramState SystemState

private def searchAuxStep (storePartialTraces : Bool) (partialTrace : List Transition)
(acceptsRemaining : ProgramState) (st : SystemState) : Array SearchState :=
  let transitions := st.possibleTransitions acceptsRemaining
  transitions.toArray.map λ t =>
    let newPT := (if storePartialTraces
                  then partialTrace ++ [t]
                  else [])
    -- TODO: add potential to sanity check
    let newST := st.applyTransition! t
    let newAC :=  acceptsRemaining.consumeTransition st t |>.clearDependencies newST
    (newPT,newAC,newST)t

private def searchAuxUpdateUnexplored (explored unexplored newtriples : Array SearchState) : Array SearchState :=
  let filterFun := λ (_,newProgState,newSysState)t =>
    let checkFun := λ (_,progState,sysState)t =>
      newProgState != progState || newSysState != sysState
    (unexplored.all checkFun && explored.all checkFun)
  Array.append (newtriples.filter filterFun) unexplored


private def searchAuxNSteps (stopAfterFirst : Bool) (storePartialTraces : Bool)
  (dontPruneCondition : SystemState → ProgramState → Bool) (n : Nat) (inputStates : Array SearchState)
 : (List ((List Transition) × SystemState)) × Array SearchState := Id.run do
 let mut unexplored := inputStates
 let mut stepsRemaining := n
 let mut found := []
 let stepFun := searchAuxStep storePartialTraces
 while h : unexplored.size > 0 && stepsRemaining > 0 do
   let (partialTrace,acceptsRemaining,st)t := unexplored[unexplored.size - 1]'
     (by rw [Bool.and_eq_true] at h
         let h' := of_decide_eq_true $ And.left h
         exact n_minus_one_le_n h')
   let newTriplesRaw := stepFun partialTrace acceptsRemaining st
   let newTriples := newTriplesRaw.filter λ (_,ps,ss)t =>
     dontPruneCondition ss ps
   unexplored := unexplored.pop
   unexplored := searchAuxUpdateUnexplored #[] unexplored newTriples
   --dbg_trace "popped {partialTrace}, remaining unexplored{unexplored.map λ (pt,_,_)t => pt} "
   stepsRemaining := stepsRemaining - 1
   found := List.append found $ filterNones $ unexplored.toList.map λ (pt,ps,ss)t =>
     if ss.finishedNoDeadlock ps
     then some (pt,ss)
     else none
   if stopAfterFirst && found.length > 0
     then return (found,unexplored)
   --dbg_trace "returning unexplored: {unexplored.map λ triple => triple.1}"
 (found,unexplored)

-- the unapologetically imperative version:
def SystemState.exhaustiveSearch (state : SystemState) (inittuple : (List (Transition)) × ProgramState)
 (dontPruneCondition : optParam (SystemState → ProgramState → Bool) (λ _ _ => true))
 (stopAfterFirst : optParam Bool false) (storePartialTraces : optParam Bool false)
 (numWorkers : optParam Nat 7) (batchSize : optParam Nat 15)
 (breadthFirst : optParam Bool false) (logProgress : optParam Bool false) :
 List ((List Transition) × SystemState) :=
match inittuple with
  | (inittransitions, accepts) =>
  let stateinit := state.applyTrace inittransitions
  let stepFun := searchAuxNSteps stopAfterFirst storePartialTraces dontPruneCondition batchSize
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
      let mut workers : Array (Task ((List ((List Transition) × SystemState)) × (Array SearchState))) := #[]
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
            if stopAfterFirst && found.length > 0 then
              unexplored := #[]
              break
            if logProgress then
              if newTriples.any λ (pt,_,_)t => pt.length > cur_size then
                cur_size := cur_size + 1
                dbg_trace "progress: partial traces of size {cur_size}"
              if explored.size.toUInt32 > thousands_explored  * 1000 then
                dbg_trace "progress: explored ≥{thousands_explored}k"
                thousands_explored := thousands_explored + 1

            unexplored := searchAuxUpdateUnexplored explored unexplored newTriples
            if stopAfterFirst && found.length > 0 then
              break
            --dbg_trace "total unexplored: {unexplored.size}"
          workers := #[]
      return found
    | .error _ => -- TODO: make this function also an Except value
    [(inittransitions,state)]

def SystemState.exhaustiveSearchLitmus
  (state : SystemState) (litmus : (List Transition) × ProgramState × Litmus.Outcome)
  (stopAfterFirst : optParam Bool false)
  (storePartialTraces : optParam Bool true) (numWorkers : optParam Nat 7)
  (batchSize : optParam Nat 15) (breadthFirst : optParam Bool false)
  (logProgress : optParam Bool false) :
  List ((List Transition) × SystemState) :=
    let (inittrans,progstate,expectedOutcome) := litmus
    let pruneFun := λ ss _ => ss.outcomePossible expectedOutcome
    state.exhaustiveSearch (inittrans,progstate) pruneFun stopAfterFirst storePartialTraces numWorkers
      batchSize breadthFirst logProgress

-- Doesn't work. Need to combine removed with requests
-- def SystemState.satisfiedRequestPairs : SystemState → List (Request × Request)
--   | state =>
--     let pairsOpt := state.satisfied.map λ (rdId, wrId) => (state.requests.val[rdId], state.requests.val[wrId])
--     let optPairs := pairsOpt.map λ (opRd, opWr) => match (opRd,opWr) with
--       | (some rd, some wr) => some (rd,wr)
--       | _ => none
--     filterNones optPairs

def runMultipleLitmus (tests : List Litmus.Test) (logProgress := false)
  (printPartialTraces := false) : List (List Litmus.Outcome) := Id.run do
    let mut tasks : Array (Task (List Litmus.Outcome)) := #[]
    for (Litmus.Test.mk initTrans initProg outcome startingState _ _) in tests do
      let task := Task.spawn λ _ =>
        let resExpl := startingState.exhaustiveSearchLitmus (initTrans,initProg,outcome)
                       (stopAfterFirst := true) (logProgress := logProgress)
        let resLitmus := Util.removeDuplicates $ resExpl.map λ (_,st) => st.outcome
        if printPartialTraces then
          let msgs := Util.removeDuplicates $ resExpl.map
            λ (pt,st) => s!"trace found for {initProg.prettyPrint}:\n {pt.map (Transition.prettyPrint st)}"
          dbg_trace (String.intercalate "\n" msgs)
          resLitmus
        else
          resLitmus -- fugly hack: dbg_trace won't work without a term after
      tasks := tasks.push task
    return tasks.map Task.get  |>.toList

def prettyPrintLitmusResult : Litmus.Test → List Litmus.Outcome → String
  | test, reslit =>
     let outcome_res := if reslit.any λ out => outcomeEqiv out test.expected
       then "✓"
       else "×"
     let litStr := s!"{test.name}. Expected: {test.expected.prettyPrint}"
     s!"litmus: {litStr}. Allowed?: {outcome_res}"

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
