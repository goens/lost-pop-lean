import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Std.Data
open Std.HashMap
open Util

namespace Pop

variable [archReqInst : ArchReq]

abbrev ProgramState := Array (Array (Transition))

def ProgramState.getAvailable (prog : ProgramState) : List (Transition) := Id.run do
  let mut res := []
  for thread in prog do
    if h : thread.size > 0 then
    res := thread[thread.size - 1]'(by apply n_minus_one_le_n h) :: res
  return res

def ProgramState.removeTransition (prog : ProgramState) (transition : (Transition))
  : ProgramState := Id.run do
  let mut res := #[]
  let mut thread' := #[]
  for thread in prog do
    thread' := thread.erase transition
    res := res.push thread'
  return res

def Request.possiblePropagateTransitions (req : Request) (state :  SystemState) : List (Transition) :=
  let threads := state.system.threads.removeAll req.propagated_to
  --dbg_trace s!"Req {req.id} has not propagated to {threads}"
  let threads_valid := threads.filter (state.canPropagate req.id)
  --dbg_trace s!"Req {req.id} can propagate to {threads_valid}"
  threads_valid.map λ th => Transition.propagateToThread req.id th

def SystemState.possiblePropagateTransitions (state :  SystemState) : List (Transition) :=
  let requests := filterNones state.requests.val.toList
  let requests_not_fully_propagated := requests.filter λ r => ! (@Request.fullyPropagated archReqInst state.system.scopes r state.system.scopes.systemScope)
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

abbrev BFSState := Array (Triple (List Transition) ProgramState SystemState)

private def BFSAuxStep (stopAtCondition : Bool) (storePartialTraces : Bool) (condition : SystemState → Bool)
(st : SystemState) (acceptsRemaining : ProgramState) (partialTrace : List Transition)
: Option (List Transition × SystemState) × BFSState :=
  let transitions := st.possibleTransitions acceptsRemaining
  let found := if condition st then some (partialTrace,st) else none
  let newTriples := if stopAtCondition && condition st
  then Array.mk []
  else
    let newPTs := transitions.map (if storePartialTraces
                                   then λ t => t::partialTrace
                                   else λ _ => [])
    -- TODO: this could yield a bug if we have two identical requests in a litmus test
    let newACs := transitions.map λ t => ProgramState.removeTransition acceptsRemaining t
    -- let _ := transitions.any λ t => if st.canApplyTransition t
    --   then dbg_trace s!"applied invalid transition {t} at {st}"
    --   true
    --   else false
    let newSTs := transitions.map λ t => st.applyTransition! t
    let newPairs := newACs.zip newSTs
    -- why do I need to make this coe explicit?
    newPTs.zip newPairs |>.map Coe.coe |>.toArray
  (found,newTriples)

private def BFSAuxUpdateUnexplored (unexplored newtriples : BFSState) : BFSState :=
  let filterFun := λ (_,newProgState,newSysState)t => !unexplored.any
    λ (_,progState,sysState)t => newProgState == progState && newSysState == sysState
  Array.append (newtriples.filter filterFun) unexplored

-- the unapologetically imperative version:
def SystemState.runBFS (state : SystemState) (inittuple : List (Transition) × ProgramState)
 (condition : SystemState → Bool) (stopAtCondition : optParam Bool false)
 (storePartialTraces : optParam Bool false) (numWorkers : optParam Nat 7):
 List (List (Transition) × SystemState) :=
match inittuple with
  | (inittransitions, accepts) =>
  let stateinit := state.applyTrace inittransitions
  let stepFun := BFSAuxStep stopAtCondition storePartialTraces condition
  match stateinit with
    | .ok startState =>
    Id.run do
      -- either save the state (memory cost) or recompute it (computational cost)
      -- we choose the former so that we can also filter out states that we've seen before
      let mut unexplored := #[([],accepts,startState)t]
      let mut found := []
      dbg_trace s!"starting state {startState}"
      dbg_trace s!"litmus requests {accepts}"
      let mut workers : Array (Task (Option (List Transition × SystemState) × BFSState)) := #[]
      while  h : unexplored.size > 0 do
          --dbg_trace s!"{unexplored.size} unexplored"
          let n := min unexplored.size (max numWorkers 1) -- at least 1
          for i in [0:n] do
            -- FIXME: Change cur!
            let some unexplored_cur := unexplored[i]?
              | panic! "index error, this shouldn't happen" -- TODO: prove i is fine
            let (partialTrace,acceptsRemaining,st)t := unexplored_cur
            let task := Task.spawn λ _ => stepFun st acceptsRemaining partialTrace
            workers := workers.push task
          for worker in workers do
            let (opFound,newTriples) := worker.get
            if let some foundNew := opFound then
              found := foundNew::found
            unexplored := BFSAuxUpdateUnexplored unexplored newTriples
            unexplored := unexplored.pop
      return found
    | .error _ => -- TODO: make this function also an Except value
    [(inittransitions,state)]


def SystemState.runBFSNoDeadlock : SystemState → List (Transition) × ProgramState →
List (List (Transition) × SystemState)
  | state, litmus => state.runBFS litmus λ _ => false

-- Doesn't work. Need to combine removed with requests
-- def SystemState.satisfiedRequestPairs : SystemState → List (Request × Request)
--   | state =>
--     let pairsOpt := state.satisfied.map λ (rdId, wrId) => (state.requests.val[rdId], state.requests.val[wrId])
--     let optPairs := pairsOpt.map λ (opRd, opWr) => match (opRd,opWr) with
--       | (some rd, some wr) => some (rd,wr)
--       | _ => none
--     filterNones optPairs

def SystemState.outcome : SystemState → List (ThreadId × Address × Value)
  | state =>
    -- TODO: this won't work for reads that stay there
    let triple := state.removed.map λ rd => (rd.thread, rd.address?.get!, rd.value?)
    triple.toArray.qsort (λ (th,ad,_) (th',ad',_) => lexble (th,ad) (th',ad')) |>.toList

-- | state, accepts => state.runDFS accepts λ _ => false

    -- let runStep := λ (acceptsRemaining, state) n => state.takeNthStep acceptsRemaining n
    -- ns.foldlM (init := (accepts, state)) runStep
    -- ns.foldlM  (init := state) λ state.takeNthStep accepts.zip ns
