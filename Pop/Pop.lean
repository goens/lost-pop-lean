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
 | acceptRequest req tid => s!"Accept ({req.toString}) at Thread {tid}"
 | propagateToThread reqid tid => s!"Propagate Request {reqid} to Thread {tid}"
 | satisfyRead readid writeid => s!"Satisfy Request {readid} with Request {writeid}"
 | dependency req => s!"Dependency on {req}"
instance : ToString (Transition) where toString := Transition.toString

def Transition.prettyPrintReq : Transition → Option String
  | acceptRequest req _ => some req.prettyPrint
  | dependency (some n) => some s!"dep (req{n})"
  | dependency none => some "dep"
  | _ => none

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

def Transition.isWriteAccept : Transition → Bool
  | .acceptRequest br _ => br.isWrite
  | _ => false

def Transition.isFenceAccept : Transition → Bool
  | .acceptRequest br _ => br.isFence
  | _ => false

def Transition.isDependency : Transition → Bool
 | dependency _ => true
 | _ => false

def Transition.getAcceptBasicRequest? : Transition → Option BasicRequest
  | .acceptRequest br _ => some br
  | _ => none

def Transition.thread? : Transition → Option ThreadId
 | acceptRequest _ tid => some tid
 | propagateToThread _ tid => some tid
 | _ => none

def Transition.prettyPrint : SystemState → Transition → String
 | state, transition => match transition.prettyPrintReq with
   | some str => s!"Accept ({str})"
   | none =>
     let reqs := state.removed.foldl RequestArray.insert state.requests
     match transition with
     | propagateToThread reqid tid =>
       match reqs.getReq? reqid with
         | some req => s!"Propagate Req{req.id} ({req.basic_type.prettyPrint}) to Thread {tid}"
         | none => s!"Propagate (UNKNOWN REQUEST {reqid}) to Thread {tid}"
     | satisfyRead readid writeid =>
       match (reqs.getReq? readid, reqs.getReq? writeid) with
       | (some read, some write) => s!"Satisfy Req{readid} ({read.basic_type.prettyPrint})"
         ++ s!" with Req{writeid} ({write.basic_type.prettyPrint})"
       | _ => s!"Satisfy (UNKNOWN REQUESTS {readid} and/or {writeid})"
     | _ => panic! "unknown case when pretty-printing {transition}"


abbrev ProgramState := Array (Array (Transition))

def ProgramState.allFilter (prog : ProgramState) (filterFun : Transition → Bool)
  : List Transition :=
  List.join $ Array.toList $ prog.map
    λ th => th.toList.filter filterFun

def ProgramState.allReads (prog : ProgramState) : List Transition :=
  prog.allFilter Transition.isReadAccept
def ProgramState.allWrites (prog : ProgramState) : List Transition :=
  prog.allFilter Transition.isWriteAccept
def ProgramState.allFences (prog : ProgramState) : List Transition :=
  prog.allFilter Transition.isFenceAccept

def SystemState.canAcceptRequest : SystemState → BasicRequest → ThreadId → Bool := Arch.acceptConstraints

def SystemState.updateOrderConstraintsPropagate (state : SystemState) : @Scope state.scopes →
RequestId → ThreadId → @OrderConstraints state.scopes
  | scope, reqId, thId =>
  match state.requests.getReq? reqId with
    | none => state.orderConstraints
    | some req =>
      let newobs := λ req' : Request =>
        req.id != req'.id && req'.propagatedTo thId &&
        -- TODO: this seems to be too weak?
        (req.isWrite && req'.isMem || req.isMem && req'.isWrite) &&
        --req.isMem && req'.isMem &&
        req.address? == req'.address? &&
        (req.thread == thId || req'.thread == thId) && -- don't sync somewhere else
        !(state.orderConstraints.lookup scope req.id req'.id) &&
        !(state.orderConstraints.lookup scope req'.id req.id)
      let newObsReqs := state.requests.filter λ r => newobs r
      let newObsConstraints := newObsReqs.map λ req' => (req.id, req'.id)
        --dbg_trace "adding {newRFConstraints} on propagate"
      state.orderConstraints.addSubscopes state.scopes.systemScope newObsConstraints

-- for predecessors
def SystemState.updateOrderConstraintsAfterPropagate (state : SystemState) : ThreadId → @OrderConstraints state.scopes
  | thId => Id.run do
    let predreqs := state.requests.filter λ r => r.isPredecessorAt thId
    let threadreqs := state.requests.filter λ r => r.thread == thId
    let mut oc := state.orderConstraints
    for req in predreqs do
      for req' in threadreqs do
        let sc := Arch.scopeIntersection state.scopes req req'
        if oc.lookup sc req.id req'.id then continue
        unless Arch.orderCondition state.scopes req req' do continue
        --dbg_trace "adding {(req.id, req'.id)} after propagate"
        oc := oc.addSubscopes sc [(req.id, req'.id)]
    oc

def SystemState.updateOrderConstraintsAccept (state : SystemState) (req : Request)
: @OrderConstraints state.scopes :=
  let threadreqs := state.idsToReqs state.seen |>.filter
    λ r => r.thread == req.thread || r.isPredecessorAt req.thread
  let newOc := Id.run do
    let mut oc := state.orderConstraints
    for req' in threadreqs do
      unless Arch.orderCondition state.scopes req' req do continue
      let sc := Arch.scopeIntersection state.scopes req' req
      oc := oc.addSubscopes sc [(req'.id, req.id)]
    oc
  let newobs := λ req' : Request =>
    req.id != req'.id &&
    -- TODO: this seems to be too weak?
    (req.isMem && req'.isWrite || req.isWrite && req'.isMem) &&
    --req.isMem && req'.isMem &&
    req.address? == req'.address?
  let propagated := state.idsToReqs state.seen |>.filter (Request.propagatedTo · req.thread)
  let newObsReqs := propagated.filter newobs |>.map λ req' => (req'.id, req.id)
  newOc.addSubscopes state.scopes.systemScope newObsReqs

def SystemState.freshId : SystemState → RequestId
  | state =>
    let removed := state.removed.map Request.id
    let active := reqIds state.requests
    let ids : List Nat := removed ++ active
    let max := ids.maximum?
    match max with
      | none => 0
      | some id => (Nat.succ id)

def SystemState.applyAcceptRequest : SystemState → BasicRequest → ThreadId → SystemState × RequestId
  | state, reqType, tId =>
  let prelimReq : Request :=
    {propagated_to := [tId], thread := tId, predecessor_at := [],
     basic_type := reqType, id := state.freshId, occurrence := 0} -- should never stay as 0
  let previous := state.requests.filter λ r => prelimReq.equivalent r
  let removed := state.removed.filter λ r => prelimReq.equivalent r
  let occurrences := previous.map Request.occurrence ++ removed.map Request.occurrence
  let req := { prelimReq with occurrence := (occurrences.maximum + 1) }
  --dbg_trace s!"accepting {req}, requests.val : {state.requests.val}"
  let requests' := state.requests.insert req
  let orderConstraints' := state.updateOrderConstraintsAccept req
  ({ requests := requests', scopes := state.scopes,
     threadTypes := state.threadTypes,
     orderConstraints := orderConstraints',
     removed := state.removed, satisfied := state.satisfied,
     removedCoherent := sorry
  }, req.id)

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
                   removed := state.removed, orderConstraints := state.orderConstraints,
                   threadTypes := state.threadTypes, scopes := state.scopes,
                   satisfied := state.satisfied, removedCoherent :=sorry}

-- def SystemState.canUnapplyPropagate : SystemState → RequestId → ThreadId → Bool
--   | state, reqId, thId =>
--   match state.requests.getReq? rId with
--     | none => false
--     | some req =>
--       let prop := req.propagatedTo thId
--       -- ...

def Request.isPropagated : Request → ThreadId → Bool
  | req, thId => req.propagated_to.elem thId

def requestBlocksPropagateRequest : SystemState → ThreadId → Request → Request → Bool
  | state, thId, propagate, block => Id.run do
    if block.id == propagate.id then
      return false
    if !block.isMem then -- fences don't propagate
      return false
    if propagate.thread == block.thread then
      for scope in state.scopes.containThread propagate.thread do
        if state.orderConstraints.lookup scope block.id propagate.id && !(block.fullyPropagated scope) then
          return true
      return false
    else
      return state.orderConstraints.lookup state.scopes.systemScope block.id propagate.id && !(block.propagatedTo thId)

def SystemState.canPropagate : SystemState → RequestId → ThreadId → Bool
  | state, reqId, thId =>
  let arch := Arch.propagateConstraints state reqId thId
  match state.requests.getReq? reqId with
  | none => false
  | some req =>
    if !req.isMem then -- fences don't propagate
      false else
    let unpropagated := !req.isPropagated thId
    let blockingReqs := state.requests.filter (requestBlocksPropagateRequest state thId req)
    --dbg_trace "can {req} propagate to thread {thId}?\n blockingReqs = {blockingReqs}"
    arch && unpropagated && blockingReqs.isEmpty

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
      threadTypes := state.threadTypes,
      removed := state.removed, satisfied := state.satisfied,
      removedCoherent := sorry}

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
        -- TODO: can/should we relax this?
        let oc := state.orderConstraints.lookup scope writeId readId
        let betweenIds := state.orderConstraints.between scope write.id read.id (reqIds state.requests)
        --dbg_trace s!"between {writeId} and {readId}: {betweenIds}"
        let between := state.idsToReqs betweenIds
        let writesToAddrBetween := between.filter λ r =>
          r.address? == write.address? && !(state.isSatisfied r.id)
        arch && oc && writesToAddrBetween.length == 0
    | _, _ => panic! s!"unknown request ({readId} or {writeId})"

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
       let requests' := state.requests.insert read'
       let orderConstraints' := state.orderConstraints
       /-
       let orderConstraints' := if betweenIds.length > 0
         then state.orderConstraints
         else state.orderConstraints.swap jointScope read.id write.id
        -/
       { requests := requests', orderConstraints := orderConstraints',
         removed := state.removed, satisfied := satisfied',
         threadTypes := state.threadTypes, removedCoherent := sorry
       }
       | false =>
       let removed' := (read'::state.removed).toArray.qsort
         (λ r₁ r₂ => Nat.ble r₁.id r₂.id) |>.toList
       let requests' := state.requests.remove readId
       { requests := requests', orderConstraints := state.orderConstraints,
         removed := removed', satisfied := satisfied',
         threadTypes := state.threadTypes, removedCoherent := sorry,
       }
   | _, _ => unreachable!

open Transition in
def SystemState.applyTransition! : SystemState → Transition → SystemState
   | state, (.acceptRequest req tId) =>
     let (acceptedState,acceptedReq) := state.applyAcceptRequest req tId
     (Arch.acceptEffects acceptedState acceptedReq tId)
   | state, .propagateToThread reqId tId =>
     let state' := (Arch.propagateEffects · reqId tId) $ state.propagate reqId tId
     {state' with orderConstraints := state'.updateOrderConstraintsAfterPropagate tId}
   | state, satisfyRead readId writeId =>
     (Arch.satisfyReadEffects · readId writeId) $ state.satisfy readId writeId
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
