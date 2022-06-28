import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Std.Data
open Std.HashMap
open Util

namespace Pop

-- TODO: Add values to writes
def mkRequest : String × Address → ThreadId → Option Transition
  | ("R", addr), thId  => some $ Pop.Transition.acceptRequest (Pop.mkRead addr) thId
  | ("W", addr), thId  => some $ Pop.Transition.acceptRequest (Pop.mkWrite addr) thId
  | ("Fence", _), thId => some $ Pop.Transition.acceptRequest (Pop.mkBarrier) thId
  | _, _ => none

def createAcceptList : List (List (String × String)) → List Transition
  | list =>
  let variablesRaw := list.map λ thread => thread.map (λ r => if r.2.length == 0 then none else some r.2)
  let variables := removeDuplicates $ filterNones $ List.join variablesRaw
  let variableNums := variables.zip (List.range variables.length)
  let variableMap := Std.mkHashMap (capacity := variableNums.length) |> variableNums.foldl λ acc (k, v) => acc.insert k v
  let replaceVar := λ (req,var) => (req, 1 + (Option.get! $ variableMap.find? var))
  let replacedVariables : List (List (String × Nat)) := list.map λ thread => thread.map replaceVar
  let fullThreads := replacedVariables.zip (List.range replacedVariables.length)
  let mkThread := λ (reqs, thId) => filterNones $ reqs.map (λ r => mkRequest r thId)
  List.join $ fullThreads.map mkThread

declare_syntax_cat request
declare_syntax_cat request_seq
declare_syntax_cat request_set
syntax "R" ident : request
syntax "W" ident : request
syntax "Fence"   : request
syntax request ";" request_seq : request_seq
syntax request : request_seq
syntax request_seq "||" request_set : request_set
syntax request_seq : request_set
syntax "<|" request_set "|>" : term

-- syntax sepBy(request_seq,  "||") : request_set

macro_rules
 | `(request| R $x:ident) => `(("R", $(Lean.quote x.getId.toString)))
 | `(request| W $x:ident) => `(("W", $(Lean.quote x.getId.toString)))
 | `(request| Fence     ) => `(("Fence", ""))

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
  let requests_active := requests_not_fully_propagated.filter λ r => (state.seen.elem r.id) && (!state.removed.elem r.id)
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
          dbg_trace trans.toString
          dbg_trace state'
          state'._runWithList (accepts.removeAll [trans]) ns
        | Except.error e => Except.error e

def SystemState.runWithList  : SystemState →  List Transition → List Nat → Except String SystemState
  | state, accepts, ns => if !accepts.all Transition.isAccept
  then throw "Running with non-accept transition inputs"
  else SystemState._runWithList state accepts ns

    -- let runStep := λ (acceptsRemaining, state) n => state.takeNthStep acceptsRemaining n
    -- ns.foldlM (init := (accepts, state)) runStep
    -- ns.foldlM  (init := state) λ state.takeNthStep accepts.zip ns 
