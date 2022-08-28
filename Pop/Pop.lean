import Pop.States
import Pop.Util

open Util

namespace Pop

variable [Arch]
instance : ArchReq := Arch.req

inductive Transition
  | acceptRequest : BasicRequest → ThreadId → Transition
  | propagateToThread : RequestId → ThreadId → Transition
  | satisfyRead : RequestId → RequestId → Transition
  | dependency : Option RequestId → Transition
 deriving BEq

instance : Inhabited (Transition) where default := Transition.acceptRequest default 0

def Transition.toString : Transition → String
 | acceptRequest req tid => s!"Accept (T{tid}): {req.prettyPrint}"
 | propagateToThread reqid tid => s!"Propagate Request {reqid} to Thread {tid}"
 | satisfyRead readid writeid => s!"Satisify Read Request {readid} with Write Request {writeid}"
 | dependency req => s!"Dependency on {req}"
instance : ToString (Transition) where toString := Transition.toString

def Transition.prettyPrintReq : Transition → Option String
  | acceptRequest req _ => some req.prettyPrint
  | dependency (some n) => some s!"dep (req{n})"
  | dependency none => some "dep"
  | _ => none

def Transition.prettyPrint : SystemState → Transition → String
 | state, transition => match transition.prettyPrintReq with
   | some str => s!"Accept ({str})"
   | none =>
     let reqs := state.removed.foldl RequestArray.insert state.requests
     match transition with
     | propagateToThread reqid tid =>
       match reqs.getReq? reqid with
         | some req => s!"Propagate ({req.basic_type.prettyPrint}) to Thread {tid}"
         | none => s!"Propagate (UNKNOWN REQUEST {reqid}) to Thread {tid}"
     | satisfyRead readid writeid =>
       match (reqs.getReq? readid, reqs.getReq? writeid) with
       | (some read, some write) => s!"Satisfy ({read.basic_type.prettyPrint})"
         ++ s!"with ({write.basic_type.prettyPrint})"
       | _ => s!"Satisfy (UNKNOWN REQUESTS {readid} and/or {writeid})"
     | _ => panic! "unknown case when pretty-printing {transition}"

def Transition.isAccept : Transition → Bool
 | acceptRequest _ _ => true
 | _ => false

def Transition.isPropagate : Transition → Bool
  | propagateToThread _ _ => true
  | _ => false

def Transition.isSatisfy : Transition → Bool
  | satisfyRead _ _ => true
  | _ => false

def Transition.isReadAccept : Transition → Bool
  | .acceptRequest br _ => br.isRead
  | _ => false

def Transition.isDependency : Transition → Bool
 | dependency _ => true
 | _ => false

abbrev ProgramState := Array (Array (Transition))

def SystemState.canAcceptRequest : SystemState → BasicRequest → ThreadId → Bool := Arch.acceptConstraints

def SystemState.updateOrderConstraintsPropagate (state : SystemState) : @Scope state.scopes →
RequestId → ThreadId → @OrderConstraints state.scopes
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
        --dbg_trace s!"{!(Arch.reorderCondition req req')}"
        req'.propagatedTo thId &&
        !(req'.propagatedTo req.thread) &&
        !(state.orderConstraints.lookup scope req.id req'.id) &&
        !(state.orderConstraints.lookup scope req'.id req.id) &&
        !(Arch.reorderCondition state.scopes req req')
      let seen := state.idsToReqs $ state.seen
      --dbg_trace s!"seen: {seen}"
      let newReqs := seen.filter conditions
      let newConstraints := newReqs.map λ req' => (req.id, req'.id) -- incoming req. goes before others
      --dbg_trace s!"new constraints: {newConstraints}"
      state.orderConstraints.addSubscopes scope newConstraints

def SystemState.updateOrderConstraintsAccept (state : SystemState) : Request → @OrderConstraints state.scopes
  | req =>
    let seen := state.idsToReqs state.seen |>.filter (Request.propagatedTo . req.thread)
    let scope := Arch.requestScope state.scopes req
    let newReqs := seen.filter λ req'  => !(Arch.reorderCondition state.scopes req' req)
    let newConstraints := newReqs.map λ req' => (req'.id, req.id)
    --dbg_trace s!"seen: {seen}, new: {newReqs}"
    state.orderConstraints.addSubscopes scope newConstraints

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
  let req : Request :=
    {propagated_to := [tId], thread := tId,
     basic_type := reqType, id := state.freshId}
  --dbg_trace s!"accepting {req}, requests.val : {state.requests.val}"
  let requests' := state.requests.insert req
  let seen' := blesort $ state.seen ++ [req.id]
  let orderConstraints' := state.updateOrderConstraintsAccept req
  { requests := requests', scopes := state.scopes, seen := seen',
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
     let scope := state.scopes.jointScope req.thread req.thread
     let succ := state.orderConstraints.successors scope rId (reqIds state.requests) == []
     let prop := req.propagated_to == [req.thread]
     succ && prop

def SystemState.unapplyAcceptRequest : SystemState → RequestId → SystemState
-- TODO: PR for multiple updates?
  | state, rId => {requests := state.requests.remove rId,
                   seen := state.seen, removed := state.removed, orderConstraints := state.orderConstraints,
                   scopes := state.scopes, satisfied := state.satisfied,
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
  let arch := Arch.propagateConstraints state reqId thId
  match state.requests.getReq? reqId with
  | none => false
  | some req =>
    let unpropagated := !req.isPropagated thId
    let scope := state.scopes.jointScope thId req.thread
    let pred := state.orderPredecessors scope reqId
    let properPred := pred.removeAll [req.id]
    --dbg_trace s!"R{req.id}.pred = {properPred}"
    let reqOps := state.requests.val.filter (λ req => match req with | none => false | some r => properPred.elem r.id)
    let reqs := filterNones reqOps.toList
    -- TODO: when here?
    --let predPropagated := reqs.map (λ r => r.fullyPropagated scope)
    let predPropagated := reqs.map (λ r => r.propagatedTo thId)
    --dbg_trace s!"R{req.id} unpropagated (T{thId}): {unpropagated}, predPropagated: {predPropagated}"
    arch && unpropagated && predPropagated.foldl (. && .) true

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
    let scope := state.scopes.jointScope thId req.thread
    let orderConstraints' := state.updateOrderConstraintsPropagate scope reqId thId
    { requests := requests', orderConstraints := orderConstraints',
      seen := state.seen, removed := state.removed, satisfied := state.satisfied,
      seenCoherent := sorry, removedCoherent := sorry,
      satisfiedCoherent := state.satisfiedCoherent
    }

def SystemState.canSatisfyRead : SystemState → RequestId → RequestId → Bool
  | state, readId, writeId =>
  let arch := Arch.satisfyReadConstraints state readId writeId
  if state.isSatisfied readId then false else
  match state.requests.val[readId.toNat]?, state.requests.val[writeId.toNat]? with
    | some (some read), some (some write) =>
      if !read.isRead || !write.isWrite then false
      else if read.address? != write.address? then false
      else if (blesort read.propagated_to) != (blesort write.propagated_to) then false
      else
        let scope := state.scopes.jointScope read.thread write.thread
        --dbg_trace "can {writeId} satisfy {readId}?"
        let oc := state.orderConstraints.lookup scope writeId readId
        let betweenIds := state.orderConstraints.between scope write.id read.id (reqIds state.requests)
        --dbg_trace s!"between {readId} and {writeId}: {betweenIds}"
        let between := state.idsToReqs betweenIds
        let writesToAddrBetween := between.filter λ r =>
          r.isWrite && r.address? == write.address? && !(state.isSatisfied r.id)
        arch && oc && writesToAddrBetween.length == 0
    | _, _ => false

def SystemState.satisfy : SystemState → RequestId → RequestId → SystemState
 | state, readId, writeId =>
 let opRead := state.requests.getReq? readId
 let opWrite := state.requests.getReq? writeId
 match opRead, opWrite with
   | some read, some write =>
     let satisfied' := (readId,writeId)::state.satisfied |>.toArray.qsort lexBLe |>.toList
     let read' := read.setValue write.value?
     match read.isPermanentRead with
       | true =>
       let jointScope := state.scopes.jointScope read.thread write.thread -- TODO: are we sure?
       let betweenIds := state.orderConstraints.between jointScope write.id read.id (reqIds state.requests)
       let requests' := state.requests.remove readId |>.insert read'
       let orderConstraints' := state.orderConstraints
       /-
       let orderConstraints' := if betweenIds.length > 0
         then state.orderConstraints
         else state.orderConstraints.swap jointScope read.id write.id
        -/
       { requests := requests', orderConstraints := orderConstraints',
         removed := state.removed, satisfied := satisfied',
         seen := state.seen, seenCoherent := sorry, removedCoherent := sorry,
         satisfiedCoherent := sorry
       }
       | false =>
       let removed' := (read'::state.removed).toArray.qsort
         (λ r₁ r₂ => Nat.ble r₁.id r₂.id) |>.toList
       let requests' := state.requests.remove readId
       { requests := requests', orderConstraints := state.orderConstraints,
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
   | state, dependency _ => state

open Transition in
def SystemState.canApplyTransition : SystemState → Transition → Bool
  | state, .acceptRequest req tId => state.canAcceptRequest req tId
  | state, .propagateToThread reqId tId => state.canPropagate reqId tId
  | state, satisfyRead readId writeId => state.canSatisfyRead readId writeId
  | state, dependency (some depId) => state.isSatisfied depId
  | _, dependency none => panic! "invalid dependency"

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
