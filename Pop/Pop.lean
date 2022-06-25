import Pop.States
import Pop.Util

open Util

namespace Pop

inductive Transition
| acceptRequest : BasicRequest → ThreadId → Transition
| propagateToThread : RequestId → ThreadId → Transition
| satisfyRead : RequestId → RequestId → Transition

def Transition.toString : Transition → String
 | acceptRequest req tid => s!"Accept ({tid}): {req}"
 | propagateToThread reqid tid => s!"Propagate Request {reqid} to Thread {tid}"
 | satisfyRead readid writeid => s!"Satisify Read Request {readid}) with Write Request {writeid}"
instance : ToString Transition where toString := Transition.toString

def SystemState.canAcceptRequest : SystemState → BasicRequest → ThreadId → Bool
 | _, _, _ => true

def SystemState.acceptRequest : SystemState → BasicRequest → ThreadId → SystemState
  | state, reqType, tId =>
  let req : Request := { propagated_to := [tId], thread := tId, basic_type := reqType, id := state.requests.val.size}
  let requests' := state.requests.insert req
  { requests := requests', system := state.system, seen := state.seen,
    orderConstraints := state.orderConstraints,
    removed := state.removed, satisfied := state.satisfied,
    seenCoherent := sorry
    removedCoherent := sorry
    satisfiedCoherent := state.satisfiedCoherent
  }

def SystemState.updateOrderConstraints (state : SystemState) : @Scope state.system.scopes → RequestId → ThreadId → @OrderConstraints state.system.scopes
  | scope, reqId, thId =>
  match state.requests.val[reqId] with
    | none => state.orderConstraints
    | some req =>
      let pred := state.idsToReqs $ state.orderConstraints.predecessors scope reqId (reqIds state.requests)
      let predReorder := pred.filter λ r => state.system.reorder_condition r req
      let predThread := predReorder.filter λ r => r.propagatedTo thId
      let newConstraints := [reqId].zip $ predThread.map Request.id
      state.orderConstraints.append scope newConstraints

def Request.isPropagated? : Request → ThreadId → Bool
  | req, thId => req.propagated_to.elem thId

def SystemState.canPropagate : SystemState → RequestId → ThreadId → Bool
  | state, reqId, thId =>
  match state.requests.val[reqId] with
  | none => false
  | some req =>
    let unpropagated := req.isPropagated? thId
    let scope := state.system.scopes.jointScope thId req.thread
    let pred := state.orderConstraints.predecessors scope reqId (reqIds state.requests)
    let reqOps := state.requests.val.filter (λ req => match req with | none => false | some r => pred.elem r.id)
    let reqs := filterNones reqOps.toList
    let predPropagated := reqs.map (λ r => r.fullyPropagated state.system.scopes.systemScope)
    unpropagated || predPropagated.foldl (. && .) true

def Request.propagate : Request → ThreadId → Request
  | req, thId => { req with propagated_to := thId :: req.propagated_to}


def SystemState.propagate : SystemState → RequestId → ThreadId → SystemState
  | state, reqId, thId =>
  let reqOpt := state.requests.val[reqId]
  match reqOpt with
  | none => state
  | some req =>
    let requests' := state.requests.insert (req.propagate thId)
    let scope := state.system.scopes.jointScope thId req.thread
    let orderConstraints' := state.updateOrderConstraints scope reqId thId
    { requests := requests', orderConstraints := orderConstraints',
      seen := state.seen, removed := state.removed, satisfied := state.satisfied,
      seenCoherent := sorry, removedCoherent := sorry,
      satisfiedCoherent := state.satisfiedCoherent
    }

def SystemState.canSatisfyRead : SystemState → RequestId → RequestId → Bool
  | state, readId, writeId =>
  if (state.satisfied.map λ x => x.1).elem readId then false else
  match state.requests.val[readId], state.requests.val[writeId] with
    | some read, some write =>
      let scope := state.system.scopes.jointScope read.thread write.thread
      let betweenIds := state.orderConstraints.between scope read.id write.id (reqIds state.requests)
      let between := state.idsToReqs betweenIds
      let writesToAddrBetween := between.filter (λ r => r.isWrite && r.address? == write.address?)
      writesToAddrBetween.length == 0
    | _, _ => false

def SystemState.satisfy : SystemState → RequestId → RequestId → SystemState
 | state, readId, writeId =>
 let satisfied' := (readId,writeId)::state.satisfied
 let removed' :=  readId::state.removed
 let requests' := state.requests.remove readId
 let orderConstraints' := state.orderConstraints.purge readId
 { requests := requests', orderConstraints := orderConstraints',
   removed := removed', satisfied := satisfied',
   seen := state.seen, seenCoherent := sorry, removedCoherent := sorry,
   satisfiedCoherent := sorry
 }

open Transition in
def SystemState.applyTransition : SystemState → Transition → Except String SystemState
  | state, (.acceptRequest req tId) =>
    if (state.canAcceptRequest req tId)
    then Except.ok $ state.acceptRequest req tId
    else throw s!"Invalid transition. Can't accept request {req} to Thread {tId}"
  | state, .propagateToThread reqId tId =>
    if (state.canPropagate reqId tId)
    then Except.ok $ state.propagate reqId tId
    else throw s!"Invalid transition. Can't propagate Request {reqId} to Thread {tId}"
  | state, satisfyRead readId writeId =>
    if (state.canSatisfyRead readId writeId)
    then Except.ok $ state.satisfy readId writeId
    else throw s!"Invalid transition. Can't satisfy Request {readId} with {writeId}"

def SystemState.applyTrace : SystemState → List Transition → Except String SystemState
  | state, transitions => transitions.foldlM SystemState.applyTransition state

def printResult : Except String SystemState → String
 | Except.ok state => state.toString
 | Except.error e => s!"Error: {e}"

end Pop
