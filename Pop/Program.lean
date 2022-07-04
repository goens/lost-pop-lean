import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Std.Data
open Std.HashMap
open Util

namespace Pop

-- TODO: Add values to writes
def mkRequest : String × Address × Value → ThreadId → Option Transition
  | ("R", addr, _), thId  => some $ Pop.Transition.acceptRequest (Pop.mkRead addr) thId
  | ("W", addr, val), thId  => some $ Pop.Transition.acceptRequest (Pop.mkWrite addr val) thId
  | ("Fence", _, _), thId => some $ Pop.Transition.acceptRequest (Pop.mkBarrier) thId
  | _, _ => none

def initZeroesUnpropagatedTransitions : List Address → List Transition
  | addresses =>
  -- Does the threadId matter? For now, using 0
  addresses.map λ addr => Pop.Transition.acceptRequest (Pop.mkWrite addr 0) 0

def SystemState.initZeroesUnpropagated! : SystemState → List Address → SystemState
  | state, addresses =>
    let writeReqs := initZeroesUnpropagatedTransitions addresses
    state.applyTrace! writeReqs

def SystemState.initZeroesUnpropagated : SystemState → List Address → Except String SystemState
  | state, addresses =>
  let writeReqs := initZeroesUnpropagatedTransitions addresses
  state.applyTrace writeReqs

def mkPropagateTransitions : List RequestId → List ThreadId → List Transition
| writeReqIds, threads =>
  List.join $ writeReqIds.map λ wr => threads.foldl (λ reqs thId => (Pop.Transition.propagateToThread wr thId) :: reqs) []

def SystemState.initZeroesPropagateTransitions : SystemState → List Address → List Transition
  | state, addresses =>
  let reqs := filterNones $ state.requests.val.toList
  -- this filter should be uneccessary if SystemState is empty
  let writeReqs := reqs.filter (λ req => req.isWrite && addresses.elem req.address?.get! && req.value? == some 0)
  let writeReqIds := writeReqs.map Request.id
  let threads := state.system.threads.removeAll [0]
  mkPropagateTransitions writeReqIds threads

def SystemState.initZeroesPropagate! : SystemState → List Address → SystemState
  | state, addresses => state.applyTrace! $ state.initZeroesPropagateTransitions addresses
def SystemState.initZeroesPropagate : SystemState → List Address → Except String SystemState
  | state, addresses => state.applyTrace $ state.initZeroesPropagateTransitions addresses

def SystemState.initZeroes! : SystemState → List Address → SystemState
  | state, addresses =>
    let unpropagated := state.initZeroesUnpropagated! addresses
    unpropagated.initZeroesPropagate! addresses

def SystemState.initZeroes : SystemState → List Address → Except String SystemState
  | state, addresses =>
    let unpropagated := state.initZeroesUnpropagated addresses
    Except.bind  unpropagated (λ st => st.initZeroesPropagate addresses)

def createAcceptList : List (List (String × String × Nat)) → List Transition × List Transition
  | list =>
  let variablesRaw := list.map λ thread => thread.map (λ r => if r.2.1.length == 0 then none else some r.2.1)
  let variables := removeDuplicates $ filterNones $ List.join variablesRaw
  let variableNums := variables.zip (List.range variables.length)
  let variableMap := Std.mkHashMap (capacity := variableNums.length) |> variableNums.foldl λ acc (k, v) => acc.insert k v
  let replaceVar := λ (req,var,val) => (req, (Option.get! $ variableMap.find? var),val)
  let replacedVariablesNat : List (List (String × Nat × Nat)) := list.map λ thread => thread.map replaceVar
  let replacedVariables : List (List (String × Address × Value)) := replacedVariablesNat.map λ l => l.map (λ (str,addr,val) => (str,Address.ofNat addr, Value.ofNat val))
  let fullThreads := replacedVariables.zip (List.range replacedVariables.length)
  let mkThread := λ (reqs, thId) => filterNones $ reqs.map (λ r => mkRequest r thId)
  let reqs := List.join $ fullThreads.map mkThread
  let initWrites := initZeroesUnpropagatedTransitions (List.range variables.length)
  let initPropagates :=  mkPropagateTransitions (List.range initWrites.length) (List.range fullThreads.length).tail! -- tail! : remove 0 because of accept
  (initWrites ++ initPropagates, reqs)

declare_syntax_cat request
declare_syntax_cat request_seq
declare_syntax_cat request_set
syntax "R" ident : request
syntax "W" ident "=" num : request
syntax "Fence"   : request
syntax request ";" request_seq : request_seq
syntax request : request_seq
syntax request_seq "||" request_set : request_set
syntax request_seq : request_set
syntax "<|" request_set "|>" : term

-- syntax sepBy(request_seq,  "||") : request_set

macro_rules
 | `(request| R $x:ident) => `(("R", $(Lean.quote x.getId.toString), 0))
 | `(request| W $x:ident = $y:num) => `(("W", $(Lean.quote x.getId.toString), $y))
 | `(request| Fence     ) => `(("Fence", "", 0))

macro_rules
  | `(request_seq| $r:request ) => `([$r])
  | `(request_seq| $r:request ; $rs:request_seq) => `($r :: $rs)

macro_rules
  | `(request_set| $r:request_seq ) => `([$r])
  | `(request_set| $r:request_seq || $rs:request_set) => `($r :: $rs)
macro_rules
  | `(<| $r |>) => `( createAcceptList $r)

def Request.possiblePropagateTransitions (req : Request) (state :  SystemState) : List Transition :=
  let threads := state.system.threads.removeAll req.propagated_to
  --dbg_trace s!"Req {req.id} has not propagated to {threads}"
  let threads_valid := threads.filter (state.canPropagate req.id)
  --dbg_trace s!"Req {req.id} can propagate to {threads_valid}"
  threads_valid.map λ th => Transition.propagateToThread req.id th

def SystemState.possiblePropagateTransitions (state :  SystemState) : List Transition :=
  let requests := filterNones state.requests.val.toList
  let requests_not_fully_propagated := requests.filter λ r => ! (@Request.fullyPropagated state.system.scopes r state.system.scopes.systemScope)
  let removedIds := state.removed.map Request.id
  let requests_active := requests_not_fully_propagated.filter λ r => (state.seen.elem r.id) && (!removedIds.elem r.id)
  -- dbg_trace s!"active requests: {requests_active}"
  List.join $ requests_active.map λ r => r.possiblePropagateTransitions state

def Request.possibleSatisfyTransitions (read : Request) (state : SystemState) : List Transition :=
  if !read.isRead then [] else
    let requests := filterNones state.requests.val.toList
    let writes_propagated_eq := requests.filter λ write => write.isWrite && write.propagated_to == read.propagated_to
    --dbg_trace s!"writes with eq propagation to {read.id}: {writes_propagated_eq}"
    let write_ids := writes_propagated_eq.map Request.id
    let writes_valid := write_ids.filter (λ write => state.canSatisfyRead read.id write) -- should be length 1
    --dbg_trace s!"valid writes for transition: {writes_valid}" 
    writes_valid.map $ Transition.satisfyRead read.id

def SystemState.possibleSatisfyTransitions (state :  SystemState) : List Transition :=
  let requests := filterNones state.requests.val.toList
  let unsatisfied_reads := requests.filter λ r => r.isRead && !(state.isSatisfied r.id)
  List.join $ unsatisfied_reads.map λ r => r.possibleSatisfyTransitions state

def SystemState.possibleTransitions (state : SystemState) (unaccepted : List Transition) :=
  let accepts := unaccepted.filter Transition.isAccept
  accepts ++ state.possibleSatisfyTransitions ++ state.possiblePropagateTransitions

def SystemState.hasUnsatisfiedReads (state : SystemState) :=
  let requests := filterNones state.requests.val.toList
  let reads := requests.filter Request.isRead
  let readids := reads.map Request.id
  let unsatisfied := readids.filter state.isSatisfied
  unsatisfied != []

def SystemState.isDeadlocked (state : SystemState) (unaccepted : List Transition) :=
  let transitions := state.possibleTransitions unaccepted
  transitions == [] && state.hasUnsatisfiedReads

-- This should be a monad transformer or smth...
def SystemState.takeNthStep (state : SystemState) (acceptRequests : List Transition) (n : Nat) : Except String (Transition × SystemState) :=
  let transitions := state.possibleTransitions acceptRequests
  --dbg_trace s!"possible transitions: {transitions}"
  if transitions.isEmpty then
    throw "No more transitions possible"
  else
    let opTrans := transitions.get? (n.mod transitions.length)
    match opTrans with
      | none => unreachable!
      | some trans => Except.map (λ st => (trans, st)) (state.applyTransition trans)

def SystemState._runWithList  : SystemState →  List Transition → List Nat → Except String SystemState
  | state, accepts, ns => match ns with
    | [] => throw "Empty transition number list"
    | n::ns =>
      let runStep := state.takeNthStep accepts n
      match runStep with
        | Except.error "No more transitions possible" => Except.ok state
        | Except.ok (trans,state') =>
          -- dbg_trace trans.toString
          -- dbg_trace state'
          state'._runWithList (accepts.removeAll [trans]) ns
        | Except.error e => Except.error e

def SystemState.runWithList  : SystemState →  List Transition → List Nat → Except String SystemState
  | state, accepts, ns => if !accepts.all Transition.isAccept
  then throw "Running with non-accept transition inputs"
  else SystemState._runWithList state accepts ns

private def appendTransitionStateAux : List (List Transition × SystemState) → Transition × SystemState  → List (List Transition × SystemState)
  | partialTrace, (trans,state) => partialTrace.map λ (transitions, _) => (trans::transitions, state)

/-
Sack overflow :

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
-- the unapologetically imperative version:
def SystemState.runBFS (state : SystemState) (inittuple : List Transition × List Transition)
 (condition : SystemState → Bool) (stopAtCondition : optParam Bool false) : List (List Transition × SystemState) :=
match inittuple with
  | (inittransitions, accepts) =>
  let stateinit := state.applyTrace inittransitions
  match stateinit with
    | .ok st =>
    Id.run do
      let mut transitions := st.possibleTransitions accepts
      let mut unexplored := transitions.map (λ tr => ([tr],accepts))  |>.toArray
      let mut found := []
      let mut partialTrace := []
      let mut acceptsRemaining := []
      while unexplored.size != 0 do
          dbg_trace s!"{unexplored.size} unexplored"
          --dbg_trace s!"{unexplored} unexplored"
          partialTrace := unexplored[unexplored.size - 1].1
          acceptsRemaining := unexplored[unexplored.size - 1].2
          let st' := st.applyTrace! partialTrace
          transitions := st'.possibleTransitions acceptsRemaining
          unexplored := unexplored.pop
          if unexplored.contains (partialTrace,acceptsRemaining) then
            dbg_trace s!"this should not happen! {unexplored} contains {(partialTrace,acceptsRemaining)}"
          --dbg_trace s!"unexplored.pop {unexplored.size}"
          -- either save the state (memory cost) or recompute it (computational cost)
          found := if condition st' then (partialTrace,st')::found else found
          unexplored := if stopAtCondition && condition st'
          then Array.mk []
          else
            let newPTs := transitions.map λ t => t::partialTrace
            let newACs := transitions.map λ t => acceptsRemaining.removeAll [t]
            let newPairs := newPTs.zip newACs |>.filter λ pair => !unexplored.contains pair
            unexplored.append newPairs.toArray
            --if unexplored.size > 11337 then
            -- dbg_trace s!"state: {st'}"
            -- dbg_trace s!"possible transitions: {transitions}"
            --unexplored := #[]

      return found
    | .error _ =>
    --dbg_trace s!"error: {e}"
    [(inittransitions,state)]


def SystemState.runBFSNoDeadlock : SystemState → List Transition × List Transition → List (List Transition × SystemState)
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
    state.removed.map λ rd => (rd.thread, rd.address?.get!, rd.value?)

-- | state, accepts => state.runDFS accepts λ _ => false

    -- let runStep := λ (acceptsRemaining, state) n => state.takeNthStep acceptsRemaining n
    -- ns.foldlM (init := (accepts, state)) runStep
    -- ns.foldlM  (init := state) λ state.takeNthStep accepts.zip ns
