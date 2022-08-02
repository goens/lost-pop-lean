import Pop.States
import Pop.Util

open Util

namespace Pop

variable [ArchReq]

inductive Transition
  | acceptRequest : BasicRequest → ThreadId → Transition
  | propagateToThread : RequestId → ThreadId → Transition
  | satisfyRead : RequestId → RequestId → Transition
 deriving BEq

instance : Inhabited (Transition) where default := Transition.acceptRequest default 0

def Transition.toString : Transition → String
 | acceptRequest req tid => s!"Accept (T{tid}): {req}"
 | propagateToThread reqid tid => s!"Propagate Request {reqid} to Thread {tid}"
 | satisfyRead readid writeid => s!"Satisify Read Request {readid} with Write Request {writeid}"
instance : ToString (Transition) where toString := Transition.toString

def Transition.isAccept : Transition → Bool
 | acceptRequest _ _ => true
 | _ => false

def Transition.isPropagate : Transition → Bool
  | propagateToThread _ _ => true
  | _ => false

def Transition.isSatisfy : Transition → Bool
  | satisfyRead _ _ => true
  | _ => false

def SystemState.canAcceptRequest : SystemState → BasicRequest → ThreadId → Bool
 | _, _, _ => true

def SystemState.updateOrderConstraintsPropagate (state : SystemState) : @Scope state.system.scopes →
RequestId → ThreadId → @OrderConstraints state.system.scopes
  | scope, reqId, thId =>
  /-
    add a constraint req, req' iff:
    * req' already propagated to thId
    * req' not propagated to req'.thread
    * req, req' not already ordered
    * req, req' can't be reoredered
    -/
  match state.requests.getReq? reqId with
    | none => state.orderConstraints
    | some req =>
      let conditions := λ req' : Request =>
        --dbg_trace s!"{req.id}, {req'.id} : "
        --dbg_trace s!"{req'.propagatedTo thId}"
        --dbg_trace s!"{!(req'.propagatedTo req.thread)}"
        --dbg_trace s!"{!(state.orderConstraints.lookup scope req.id req'.id)}"
        --dbg_trace s!"{!(state.orderConstraints.lookup scope req'.id req.id)}"
        --dbg_trace s!"{!(state.system.reorder_condition req req')}"
        req'.propagatedTo thId &&
        !(req'.propagatedTo req.thread) &&
        !(state.orderConstraints.lookup scope req.id req'.id) &&
        !(state.orderConstraints.lookup scope req'.id req.id) &&
        !(state.system.reorder_condition req req')
      let seen := state.idsToReqs $ state.seen
      --dbg_trace s!"seen: {seen}"
      let newReqs := seen.filter conditions
      let newConstraints := newReqs.map λ req' => (req.id, req'.id) -- incoming req. goes before others
      --dbg_trace s!"new constraints: {newConstraints}"
      state.orderConstraints.add_subscopes scope newConstraints

def SystemState.updateOrderConstraintsAccept (state : SystemState) : Request → @OrderConstraints state.system.scopes
  | req =>
    let seen := state.idsToReqs state.seen |>.filter (Request.propagatedTo . req.thread)
    let scope := state.system.requestScope req
    let newReqs := seen.filter λ req'  => !(state.system.reorder_condition req' req)
    let newConstraints := newReqs.map λ req' => (req'.id, req.id)
    --dbg_trace s!"seen: {seen}, new: {newReqs}"
    state.orderConstraints.add_subscopes scope newConstraints

def SystemState.freshId : SystemState → RequestId
  | state =>
    let removed := state.removed.map Request.id
    let active := reqIds state.requests
    let ids : List Nat := removed ++ active
    let max := ids.maximum?
    match max with
      | none => 0
      | some id => (Nat.succ id)

def SystemState.applyAcceptRequest : SystemState → BasicRequest → ThreadId → SystemState
  | state, reqType, tId =>
  let req : Request := { propagated_to := [tId], thread := tId, basic_type := reqType, id := state.freshId}
  --dbg_trace s!"accepting {req}, requests.val : {state.requests.val}"
  let requests' := state.requests.insert req
  let seen' := blesort $ state.seen ++ [req.id]
  let orderConstraints' := state.updateOrderConstraintsAccept req
  { requests := requests', system := state.system, seen := seen',
    orderConstraints := orderConstraints',
    removed := state.removed, satisfied := state.satisfied,
    seenCoherent := sorry
    removedCoherent := sorry
    satisfiedCoherent := sorry
  }

def SystemState.canUnapplyRequest : SystemState → RequestId → Bool
  | state, rId =>
  match state.requests.getReq? rId with
   | none => false
   | some req =>
     let scope := state.system.scopes.jointScope req.thread req.thread
     let succ := state.orderConstraints.successors scope rId (reqIds state.requests) == []
     let prop := req.propagated_to == [req.thread]
     succ && prop

def SystemState.unapplyAcceptRequest : SystemState → RequestId → SystemState
-- TODO: PR for multiple updates?
  | state, rId => {requests := state.requests.remove rId,
                   seen := state.seen, removed := state.removed, orderConstraints := state.orderConstraints,
                   system := state.system, satisfied := state.satisfied,
                   seenCoherent := sorry, removedCoherent :=sorry, satisfiedCoherent := sorry}

-- def SystemState.canUnapplyPropagate : SystemState → RequestId → ThreadId → Bool
--   | state, reqId, thId =>
--   match state.requests.getReq? rId with
--     | none => false
--     | some req =>
--       let prop := req.propagatedTo thId
--       -- ...

def Request.isPropagated : Request → ThreadId → Bool
  | req, thId => req.propagated_to.elem thId

def SystemState.canPropagate : SystemState → RequestId → ThreadId → Bool
  | state, reqId, thId =>
  match state.requests.getReq? reqId with
  | none => false
  | some req =>
    let unpropagated := !req.isPropagated thId
    let scope := state.system.scopes.jointScope thId req.thread
    let pred := state.orderConstraints.predecessors scope reqId (reqIds state.requests)
    let properPred := pred.removeAll [req.id]
    --dbg_trace s!"R{req.id}.pred = {properPred}"
    let reqOps := state.requests.val.filter (λ req => match req with | none => false | some r => properPred.elem r.id)
    let reqs := filterNones reqOps.toList
    -- TODO: when here?
    --let predPropagated := reqs.map (λ r => r.fullyPropagated scope)
    let predPropagated := reqs.map (λ r => r.propagatedTo thId)
    --dbg_trace s!"R{req.id} unpropagated (T{thId}): {unpropagated}, predPropagated: {predPropagated}"
    unpropagated && predPropagated.foldl (. && .) true

def Request.propagate : Request → ThreadId → Request
  | req, thId =>
    let sorted := (thId :: req.propagated_to).toArray.qsort (λ x y => Nat.ble x y)
    { req with propagated_to := sorted.toList}


def SystemState.propagate : SystemState → RequestId → ThreadId → SystemState
  | state, reqId, thId =>
  match state.requests.getReq? reqId with
  | none => state
  | some req =>
    let requests' := state.requests.insert (req.propagate thId)
    let scope := state.system.scopes.jointScope thId req.thread
    let orderConstraints' := state.updateOrderConstraintsPropagate scope reqId thId
    { requests := requests', orderConstraints := orderConstraints',
      seen := state.seen, removed := state.removed, satisfied := state.satisfied,
      seenCoherent := sorry, removedCoherent := sorry,
      satisfiedCoherent := state.satisfiedCoherent
    }

def SystemState.canSatisfyRead : SystemState → RequestId → RequestId → Bool
  | state, readId, writeId =>
  if (state.satisfied.map λ x => x.1).elem readId then false else
  match state.requests.val[readId.toNat]?, state.requests.val[writeId.toNat]? with
    | some (some read), some (some write) =>
      if !read.isRead || !write.isWrite then false
      else if read.address? != write.address? then false
      else if (blesort read.propagated_to) != (blesort write.propagated_to) then false
      else
        let scope := state.system.scopes.jointScope read.thread write.thread
        --dbg_trace "can {writeId} satisfy {readId}?"
        let oc := state.orderConstraints.lookup scope writeId readId
        let betweenIds := state.orderConstraints.between scope write.id read.id (reqIds state.requests)
        --dbg_trace s!"between {readId} and {writeId}: {betweenIds}"
        let between := state.idsToReqs betweenIds
        let writesToAddrBetween := between.filter (λ r => r.isWrite && r.address? == write.address?)
        oc && writesToAddrBetween.length == 0
    | _, _ => false

def SystemState.satisfy : SystemState → RequestId → RequestId → SystemState
 | state, readId, writeId =>
 let opRead := state.requests.getReq? readId
 let opWrite := state.requests.getReq? writeId
 match opRead, opWrite with
   | some read, some write =>
      let satisfied' := (readId,writeId)::state.satisfied |>.toArray.qsort lexble |>.toList
      let read' := read.setValue write.value?
      let removed' :=  (read'::state.removed).toArray.qsort (λ r₁ r₂ => Nat.ble r₁.id r₂.id) |>.toList
      let requests' := state.requests.remove readId
      let orderConstraints' := state.orderConstraints --.purge readId
      { requests := requests', orderConstraints := orderConstraints',
        removed := removed', satisfied := satisfied',
        seen := state.seen, seenCoherent := sorry, removedCoherent := sorry,
        satisfiedCoherent := sorry
      }
   | _, _ => unreachable!

open Transition in
def SystemState.applyTransition! : SystemState → Transition → SystemState
   | state, (.acceptRequest req tId) => state.applyAcceptRequest req tId
   | state, .propagateToThread reqId tId => state.propagate reqId tId
   | state, satisfyRead readId writeId => state.satisfy readId writeId

open Transition in
def SystemState.canApplyTransition : SystemState → Transition → Bool
  | state, .acceptRequest req tId => state.canAcceptRequest req tId
  | state, .propagateToThread reqId tId => state.canPropagate reqId tId
  | state, satisfyRead readId writeId => state.canSatisfyRead readId writeId

open Transition in
def SystemState.applyTransition : SystemState → Transition → Except String (SystemState)
  | state, t =>
    if state.canApplyTransition t
    then Except.ok $ state.applyTransition! t
    else throw s!"Invalid transition {t}."

def SystemState.applyTrace : SystemState → List (Transition) → Except String (SystemState)
  | state, transitions => transitions.foldlM SystemState.applyTransition state

def SystemState.applyTrace! : SystemState → List (Transition) → SystemState
  | state, transitions => transitions.foldl SystemState.applyTransition! state

def printResult : Except String (SystemState) → String
 | Except.ok state => state.toString
 | Except.error e => s!"Error: {e}"

end Pop
