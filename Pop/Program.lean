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

abbrev ProgramState := Array (Array Transition)

def ProgramState.getAvailable (prog : ProgramState) : List Transition := Id.run do
  let mut res := []
  for thread in prog do
    if thread.size > 0 then
      res := thread[thread.size - 1] :: res
  return res

def ProgramState.removeTransition (prog : ProgramState) (transition : Transition)
  : ProgramState := Id.run do
  let mut res := #[]
  let mut thread' := #[]
  for thread in prog do
    thread' := thread.erase transition
    res := res.push thread'
  return res

-- create accepts in a per-thread basis
def createAcceptList : List (List (String × String × Nat)) → List Transition × ProgramState
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
  let reqs := fullThreads.map λ t => mkThread t |>.toArray
  let initWrites := initZeroesUnpropagatedTransitions (List.range variables.length)
  let initPropagates :=  mkPropagateTransitions (List.range initWrites.length) (List.range fullThreads.length).tail! -- tail! : remove 0 because of accept
  (initWrites ++ initPropagates, reqs.toArray)

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
def SystemState.takeNthStep (state : SystemState) (acceptRequests : ProgramState) (n : Nat) : Except String (Transition × SystemState) :=
  let transitions := state.possibleTransitions acceptRequests
  --dbg_trace s!"possible transitions: {transitions}"
  if transitions.isEmpty then
    throw "No more transitions possible"
  else
    let opTrans := transitions.get? (n.mod transitions.length)
    match opTrans with
      | none => unreachable!
      | some trans => Except.map (λ st => (trans, st)) (state.applyTransition trans)

def SystemState._runWithList  : SystemState →  ProgramState → List Nat → Except String SystemState
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

def SystemState.runWithList  : SystemState →  ProgramState → List Nat → Except String SystemState
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
-- the unapologetically imperative version:
def SystemState.runBFS (state : SystemState) (inittuple : List Transition × ProgramState) (condition : SystemState → Bool)
  (stopAtCondition : optParam Bool false) (saveStates : optParam Bool true) (saveTraces : optParam Bool true)
 : List (List Transition × SystemState) :=
match inittuple with
  | (inittransitions, accepts) =>
  let stateinit := state.applyTrace inittransitions
  match stateinit with
    | .ok startState =>
    if !saveStates && !saveTraces then
      panic! "BFS can't run without saving states or traces."
    else Id.run do
      let mut transitions := startState.possibleTransitions accepts
      -- either save the state (memory cost) or recompute it (computational cost)
      -- we choose the former so that we can also filter out states that we've seen before
      let mut unexplored := transitions.map (λ tr => ([tr],accepts))  |>.toArray
      let mut states := if saveStates then List.replicate transitions.length startState |>.toArray else #[]
      let mut found := []
      let mut partialTrace := [transitions.head!]
      let mut acceptsRemaining := #[]
      dbg_trace s!"starting state {startState}"
      dbg_trace s!"litmus requests {accepts}"
      while unexplored.size != 0 do
          --dbg_trace s!"{unexplored.size} unexplored"
          --dbg_trace s!"{unexplored} unexplored"
          partialTrace := unexplored[unexplored.size - 1].1
          acceptsRemaining := unexplored[unexplored.size - 1].2
          let st := if saveStates
            then states[unexplored.size - 1]
            else startState.applyTrace! partialTrace
          transitions := st.possibleTransitions acceptsRemaining
          --acceptsRemaining := acceptsRemaining.map $ List.removeAll [transition]
          unexplored := unexplored.pop
          states := if saveStates then states.pop else states
          unexplored := unexplored.pop
          -- if unexplored.any (λ (_,a,s) => a == acceptsRemaining && s == st') then
          --   dbg_trace s!"this should not happen! {unexplored} contains {(partialTrace,acceptsRemaining)}"
          --dbg_trace s!"unexplored.pop {unexplored.size}"
          found := if condition st
            then if saveTraces then (partialTrace,st)::found else ([],st)::found
            else found
          unexplored := if stopAtCondition && condition st
          then Array.mk []
          else
            let newPTs := if saveTraces then transitions.map λ t => t::partialTrace else transitions.map λ t => [t]
            -- TODO: this could yield a bug if we have two identical requests in a litmus test
            let newACs := transitions.map λ t => ProgramState.removeTransition acceptsRemaining t
            -- let _ := transitions.any λ t => if st.canApplyTransition t
            --   then dbg_trace s!"applied invalid transition {t} at {st}"
            --   true
            --   else false
            let newSTs := if saveStates
              then transitions.map (λ t => st.applyTransition! t)
              else []
            /-
            Here we filter program/system-state pairs that are equal, pruning a part of the search tree.
            This can be improved, however, in particular as there's a bunch of inconsequential permutations
            of the order in which requests are propagated, which could all be collapsed into one
            If we can be *sure* that they are inconsequential, that is, which I'm not sure if we can know that
            at this point in the computation...
            -/
            if saveStates then
              let newPairs := newACs.zip newSTs
              let triples : List (List Transition × ProgramState × SystemState) := newPTs.zip newPairs |>.filter
                λ (_,pair) => !(unexplored.zip states).any λ ((_,ps'),ss') => pair == (ps',ss')
              unexplored.append $ triples.map (λ (pt,(ac,_)) => (pt,ac)) |>.toArray
            else
              -- This is a very costly computation, as we have to apply the traces many times...
              let newPairs := newPTs.zip newACs |>.filter
                λ (pt,ac) => !unexplored.any
                  λ (pt',ac') => ac == ac' && startState.applyTrace! pt == startState.applyTrace! pt'
              unexplored.append newPairs.toArray
            --if unexplored.size > 11337 then
            -- dbg_trace s!"state: {st}"
            -- dbg_trace s!"possible transitions: {transitions}"
            --unexplored := #[]
      return found
    | .error _ =>
    --dbg_trace s!"error: {e}"
    [(inittransitions,state)]


def SystemState.runBFSNoDeadlock : SystemState → List Transition × ProgramState → List (List Transition × SystemState)
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
