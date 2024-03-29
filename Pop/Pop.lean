-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

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

def ProgramState.all (prog : ProgramState) : List Transition := prog.allFilter (λ _ => true)

def ProgramState.allReads (prog : ProgramState) : List Transition :=
  prog.allFilter Transition.isReadAccept
def ProgramState.allWrites (prog : ProgramState) : List Transition :=
  prog.allFilter Transition.isWriteAccept
def ProgramState.allFences (prog : ProgramState) : List Transition :=
  prog.allFilter Transition.isFenceAccept

def Request.isFenceLike (req : Request) : Bool := !req.blockingSemantics.isEmpty
def Request.blocksOnReads (req : Request) : Bool :=
  req.blockingSemantics.contains BlockingKinds.Read2ReadPred ||
  req.blockingSemantics.contains BlockingKinds.Read2ReadNoPred ||
  req.blockingSemantics.contains BlockingKinds.Read2WritePred ||
  req.blockingSemantics.contains BlockingKinds.Read2WriteNoPred

def Request.blocksOnWrites (req : Request) : Bool :=
  req.blockingSemantics.contains BlockingKinds.Write2Read ||
  req.blockingSemantics.contains BlockingKinds.Write2Write

def Request.blocksOnPreds (req : Request) : Bool :=
  req.blockingSemantics.contains BlockingKinds.Read2ReadPred ||
  req.blockingSemantics.contains BlockingKinds.Read2WritePred

def memopsNotDone (state : SystemState) (fenceLike : Request) : List Request :=
    let preds := state.requests.filter λ r => r.isPredecessorAt fenceLike.thread && state.orderConstraints.lookup (state.scopes.reqThreadScope fenceLike) r.id fenceLike.id
    let memopsOnThread := state.requests.filter λ r => r.isMem &&  r.thread == fenceLike.thread && !r.isSatisfied &&
                          state.orderConstraints.lookup (state.scopes.reqThreadScope fenceLike) r.id fenceLike.id
    (memopsOnThread ++ preds).filter λ r =>
        let scope := Arch.scopeIntersection state.scopes r fenceLike
        !(state.isSatisfied r.id || r.fullyPropagated scope) && r.id != fenceLike.id

def readsDone (state : SystemState) (fenceLike : Request) : Bool :=
  let reads := memopsNotDone state fenceLike |>.filter Request.isRead
  reads.isEmpty

def writesDone (state : SystemState) (fenceLike : Request) : Bool :=
  let writes := memopsNotDone state fenceLike |>.filter λ w => w.isWrite && w.thread == fenceLike.thread
  writes.isEmpty

def predsDone (state : SystemState) (fenceLike : Request) : Bool :=
  let preds := memopsNotDone state fenceLike |>.filter λ p => p.isPredecessorAt fenceLike.thread
  preds.isEmpty

def SystemState.getPairedRequest? : SystemState → RequestId → Option Request
  | state, reqId => match state.requests.getReq? reqId with
    | none => none
    | some req => match req.pairedRequest? with
      | none => none
      | some id => state.findMaybeRemoved? id

def SystemState.rmwGetPreviousWrite? : SystemState → RequestId → Option Request
  | state, reqId => match state.requests.getReq? reqId with
    | none => none
    | some req => if !req.isWrite then none
      else match state.getPairedRequest? reqId with
        | none => none
        | some rmwRead =>
          let satisifiedWrites := state.satisfied.filter
            (λ (r,_) => r == rmwRead.id) |>.map
              λ (_,w) => w
          match satisifiedWrites.head? with
            | none => none
            | some writeId =>
              state.requests.getReq? writeId

/-
  | state, readId => match state.requests.getReq? readId with
    | none => none
    | some read =>
      let ocLookup := state.orderConstraints.lookup (state.scopes.reqThreadScope read)
      let readThreadRequests := state.requests.filter (·.thread == read.thread)
      let afterRead := readThreadRequests.filter
                 λ req => ocLookup readId req.id
      let firstAfterRead := afterRead.filter λ req => afterRead.all
                   λ req' => req.id == req'.id || ocLookup req.id req'.id
      firstAfterRead.head?
-/

-- TODO: add also for atomics
def SystemState.blockedOnRequests (state : SystemState) : List Request := Id.run do
  let fences := state.requests.filter Request.isFenceLike
  let mut res := []
  for fence in fences do
    if fence.blocksOnReads && !(readsDone state fence) then
      res := res ++ [fence]
      continue
    if fence.blocksOnWrites && !(writesDone state fence) then
      res := res ++ [fence]
      continue
    if fence.blocksOnPreds && !(predsDone state fence) then
      res := res ++ [fence]
      continue
  return res

def propagateConstraintsAux (state : SystemState) (req : Request) (blocking : List Request) : Bool :=
  if blocking.isEmpty then
    true else
  if !req.isMem then -- fences don't propagate
    false else
  --dbg_trace (String.intercalate "\n" $ blocking.map λ fenceLike => s!"R{fenceLike.id}{fenceLike.blockingSemantics} blocking {req.id}? memops: {memopsNotDone state fenceLike}\n....reads: {readsDone state fenceLike}, writes: {writesDone state fenceLike}, preds: {predsDone state fenceLike}")
  if req.isRead then blocking.all λ fenceLike =>
      (!fenceLike.blockingSemantics.contains .Read2ReadNoPred || readsDone state fenceLike) &&
      (!fenceLike.blockingSemantics.contains .Read2ReadPred   || (readsDone state fenceLike && predsDone state fenceLike)) &&
      (!fenceLike.blockingSemantics.contains .Write2Read      || writesDone state fenceLike)
 else if req.isWrite then blocking.all λ fenceLike =>
      (!fenceLike.blockingSemantics.contains .Read2WriteNoPred || readsDone state fenceLike) &&
      (!fenceLike.blockingSemantics.contains .Read2WritePred   || (readsDone state fenceLike && predsDone state fenceLike)) &&
      (!fenceLike.blockingSemantics.contains .Write2Write      || writesDone state fenceLike)
 else panic! s!"unknown request type ({req})"

def addNewPredecessors (state : SystemState) (write read : Request) (thId : ThreadId) : SystemState := Id.run do
  if write.isWrite && read.isRead && write.address? == read.address? && read.thread == thId  &&
  Arch.predecessorConstraints state write.id read.id then
    return state.updateRequest $ write.makePredecessorAt thId
  else
    return state

-- TODO: this is for atomics (cannot fail)
def SystemState.rmwPairsBlocking : SystemState → List (Request × Request)
  | state => []
  /-
    let atomics := state.requests.filter Request.isAtomic
    -- quadratic, but shouldn't often by many pairs anyway
    let rmw_pairs := filterNones $ atomics.map
      λ req => if !req.isRead then none else
        let succ_write? := state.getPairedRequest? req.id
        match succ_write? with
          | none => none
          | some write => some (req,write)
    rmw_pairs.filter
      λ (read, write) => !(read.propagated_to == write.propagated_to)
      -/

def SystemState.canAcceptRequest : SystemState → BasicRequest → ThreadId → Bool
  | state, br, thId =>
    if state.rmwPairsBlocking.isEmpty then
      Arch.acceptConstraints state br thId
    else
      false

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
      state.orderConstraints.addSubscopes state.scopes.systemScope newObsConstraints

-- TODO: refactor this all into one update, including the predecessors
-- for predecessors
def SystemState.updateOrderConstraintsAfterPropagate (state : SystemState) : ThreadId → @OrderConstraints state.scopes
  | thId => Id.run do
    let predreqs := state.requests.filter λ r => r.isPredecessorAt thId
    let threadreqs := state.requests.filter λ r => r.thread == thId
    let mut oc := state.orderConstraints
    for req in predreqs do
      for req' in threadreqs do
        let sc := Arch.scopeIntersection state.scopes req req'
        if req.id == req'.id then continue
        if oc.lookup sc req.id req'.id then continue
        if oc.lookup sc req'.id req.id then continue
        if Arch.orderCondition state.scopes req req' then
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

/-
 * A predecessor should behave *as if* it was in that same thread.
 * We add edge between predecessor and fence always (?):  maybe only for ≥release?
 * Add predecessor only at RF (not at propagate)
-/
def SystemState.applyAcceptRequest : SystemState → BasicRequest → ThreadId → SystemState × RequestId
  | state, reqType, tId => Id.run do
  let prelimReq : Request :=
    {propagated_to := [tId], thread := tId, predecessor_at := [], pairedRequest? := none,
     basic_type := reqType, id := state.freshId, occurrence := 0} -- should never stay as 0
  -- The write updates both the read and itself for the rmw pair.
   -- TODO: get the other request here
  let previous := state.requests.filter λ r => prelimReq.equivalent r
  let removed := state.removed.filter λ r => prelimReq.equivalent r
  let occurrences := previous.map Request.occurrence ++ removed.map Request.occurrence
  let req := { prelimReq with occurrence := (occurrences.maximum + 1) }
  let pairedRequest? := if reqType.isWrite && (reqType.isTransactional || reqType.isAtomic) then
    let threadReads := state.requests.filter
      λ r => r.thread == tId && r.isRead && r.address? == req.address? && (r.isAtomic || r.isTransactional)
    let ocLookup := state.orderConstraints.lookup (state.scopes.jointScope tId tId)
    let paired := threadReads.filter
      λ r => threadReads.all
       λ r' => r.id == r'.id || ocLookup r'.id r.id
    paired.head?
    else none
  --dbg_trace s!"accepting {req}, requests.val : {state.requests.val}"
  let requests' :=
    match pairedRequest? with
      | none => state.requests.insert req
      | some paired =>
        let paired' := {paired with pairedRequest? := some req.id}
        let req' := {req with pairedRequest? := some paired.id}
        state.requests.insert req' |>.insert paired'
  let orderConstraints' := state.updateOrderConstraintsAccept req
  let mut st :=
   { requests := requests', scopes := state.scopes,
     threadTypes := state.threadTypes,
     orderConstraints := orderConstraints',
     removed := state.removed, satisfied := state.satisfied,
     removedCoherent := sorry
  }
  let writesOnThread := state.requests.filter λ w => w.isWrite && w.propagatedTo tId
  for write in writesOnThread do
    st := addNewPredecessors st write (st.requests.getReq! req.id) tId
  return (st, req.id)

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

/-
A RMW can either fail or succeed.

If atomicity is violated (i.e. another write comes in-between the RMW-read and the RMW-write) then
the write will fail. If the RMW-write starts propagating (after the RMW-read has been satisfied) or is used
to satisfy another read, then the RMW-write succeeds. In this case, we need to preserve the atomicity
condition. This means that all writes to that same address need to be before the write read by the RMW-read
or after the RMW-write. In particular, a write is blocked from propagating to the RMW's thread if it would break
this invariant.
-/
def Request.conditionalValue? : Request → Option ConditionalValue
  | req => req.basic_type.conditionalValue?

def Request.conditionalSucceeded : Request → Bool
  | req => match req.conditionalValue? with
    | some (.const _) => true
    | some _ => false
    | none => false

def Request.conditionalFailed : Request → Bool
  | req => match req.conditionalValue? with
    | some .failed => true
    | some _ => false
    | none => false

def Request.conditionalUndecided : Request → Bool
  | req => match req.conditionalValue? with
    | some .failed => false
    | some (.const _) => false
    | some _ => true
    | none => false

def Request.conditionalTentativeOrSuccessful : Request → Bool
  | req => match req.conditionalValue? with
    | some (.const _) => true
    | some (.tentative _) => true
    | _ => false

def SystemState.inFlightTransactions : SystemState → List (Request × Request)
  | state =>
    let satisfiedReads := filterNones $ state.satisfied.map λ (r_id,w_id) =>
      match (state.requests.getReq? r_id, state.requests.getReq? w_id) with
        | (some read, some write) => some (read, write)
        | _ => none
    satisfiedReads.filter λ (read, _) => read.isTransactional

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

def SystemState.transactionsBlocking : SystemState → RequestId → ThreadId → Bool
  | state, reqId, thId =>
    match state.requests.getReq? reqId with
      | none => false
      | some req =>
      if !req.isWrite then false else
        let inFlight := state.inFlightTransactions.map (λ (_,rd) => state.getPairedRequest? rd.id)
          |> filterNones |>.filter (λ wr => wr.address? == req.address? && wr.thread == thId)
        let scope := state.scopes.jointScope thId req.thread
        -- the incoming request must already be ordered with all in-flight RMWs
        inFlight.any λ wr => !state.orderConstraints.lookup scope wr.id reqId && !state.orderConstraints.lookup scope reqId wr.id

def SystemState.canPropagate : SystemState → RequestId → ThreadId → Bool
  | state, reqId, thId =>
  let arch := Arch.propagateConstraints state reqId thId
  match state.requests.getReq? reqId with
  | none => false
  | some req =>
    if !req.isMem then -- fences don't propagate
      false else
    if (req.isAtomic || req.isTransactional) && req.isWrite && !req.conditionalTentativeOrSuccessful then -- can't propagate until decided
      false else
    if state.transactionsBlocking reqId thId then
      false else
    let unpropagated := !req.isPropagated thId
    let blockingReqs := state.requests.filter (requestBlocksPropagateRequest state thId req)
    let blockingFenceLikes := state.blockedOnRequests.filter
        λ r => r.thread == req.thread &&
        (state.orderConstraints.lookup (state.scopes.reqThreadScope req) r.id req.id || r.id == req.id)
    --dbg_trace "propagate {reqId}, \n{blockingFenceLikes} not blocked? {propagateConstraintsAux state req blockingFenceLikes}"
    let fenceLikes := propagateConstraintsAux state req blockingFenceLikes
    --dbg_trace "can {req} propagate to thread {thId}?\n blockingReqs = {blockingReqs}"
    let rmw_pairs_done := state.rmwPairsBlocking.all λ (read, write) => write.id == reqId && read.propagatedTo thId
    arch && unpropagated && blockingReqs.isEmpty && fenceLikes && rmw_pairs_done

def SystemState.cleanupTransactions : SystemState → SystemState
   | state =>
     let rmwWrites := state.requests.filter
       λ req => req.isWrite && (req.isTransactional || req.isAtomic)
     rmwWrites.foldl (init := state)
       λ state rmwWrite =>
         match state.rmwGetPreviousWrite? rmwWrite.id with
           | none => state
           | some previousWrite =>
               let otherWrites := state.requests.filter
                 λ r => r.isWrite && r.address? == rmwWrite.address? &&
                        r.id != rmwWrite.id && r.id != previousWrite.id
               let failedWriteBetween := otherWrites.any
                 λ write' =>
                   -- write' is between the original write (that the RMW-read `read` is being satisfied by) and the RMW-write.
                   let scope1 := state.scopes.jointScope previousWrite.thread write'.thread
                   state.orderConstraints.lookup scope1 previousWrite.id write'.id &&
                   let scope2 := state.scopes.jointScope rmwWrite.thread write'.thread
                   state.orderConstraints.lookup scope2 write'.id rmwWrite.id
               let failedOtherRMW := otherWrites.filter
                 (λ req => Option.map Request.id (state.rmwGetPreviousWrite? req.id) == some previousWrite.id)
                 |>.any Request.conditionalSucceeded
               let failed := failedWriteBetween || failedOtherRMW
               let rmwWrite' := if failed then
                   rmwWrite.updateValue none else
                   -- this is part of satisfy, but we do it here anyway (idempotent on const c).
                   if !rmwWrite.conditionalTentativeOrSuccessful then
                       rmwWrite.updateValue previousWrite.value?
                   else
                       rmwWrite
               let removedWrites := state.requests.filter Request.conditionalFailed ++
                 if failed then [rmwWrite'] else []
               let removed' := (removedWrites ++ state.removed).toArray.qsort
                 (λ r₁ r₂ => Nat.ble r₁.id r₂.id) |>.toList
               let requestsRemoved := removedWrites.foldl (λ arr req => arr.remove req.id) state.requests
               -- Don't reeinsert removed rmwWrite' if failed.
               let requests' := if failed then requestsRemoved else requestsRemoved.insert rmwWrite'
               {state with requests := requests', removed := removed', removedCoherent := sorry}


def Request.propagate : Request → ThreadId → Request
  | req, thId =>
    let sorted := (thId :: req.propagated_to).toArray.qsort (λ x y => Nat.ble x y)
    { req.validateWrite with propagated_to := sorted.toList}

def SystemState.propagate : SystemState → RequestId → ThreadId → SystemState
  | state, reqId, thId => Id.run do
  match state.requests.getReq? reqId with
  | none => state
  | some req_old =>
    let req := req_old.propagate thId
    let requests' := state.requests.insert req
    let scope := state.scopes.jointScope thId req.thread
    let orderConstraints' := state.updateOrderConstraintsPropagate scope reqId thId
    let mut res := { state with
      requests := requests', orderConstraints := orderConstraints', removedCoherent := sorry}
    let successors := res.orderConstraints.successors (res.scopes.jointScope req.thread thId) reqId res.seen
    for reqId' in successors do
      if let some req' := res.requests.getReq? reqId' then
        res := addNewPredecessors res req req' thId
    return res.cleanupTransactions

def SystemState.canSatisfyRead : SystemState → RequestId → RequestId → Bool
  | state, readId, writeId =>
  let arch := Arch.satisfyReadConstraints state readId writeId
  if state.isSatisfied readId then false else
  match state.requests.val[readId.toNat]?, state.requests.val[writeId.toNat]? with
    | some (some read), some (some write) =>
      if !read.isRead || !write.isWrite then false
      else if read.address? != write.address? then false
      else if write.conditionalFailed then false
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
          r.address? == write.address? && !(state.isSatisfied r.id) && !r.conditionalFailed -- TODO: sure about this?
        let rmwPairs := state.rmwPairsBlocking
        arch && oc && writesToAddrBetween.length == 0 && (write.conditionalTentativeOrSuccessful )&& rmwPairs.isEmpty
    | _, _ => panic! s!"unknown request ({readId} or {writeId})"

def SystemState.alreadyOrdered : SystemState → RequestId → RequestId → Bool
  | state, reqId, reqId' =>
    match state.requests.getReq? reqId, state.requests.getReq? reqId' with
      | some req, some req' =>
        let scope := state.scopes.jointScope req.thread req'.thread
        state.orderConstraints.lookup scope reqId reqId' || state.orderConstraints.lookup scope reqId' reqId
      | _, _ => false

def SystemState.validateWrite : SystemState → RequestId → RequestArray
  | state, writeId =>
    match state.requests.getReq? writeId with
      | none => state.requests
      | some rmwWrite => if !rmwWrite.isWrite then state.requests else
        match state.rmwGetPreviousWrite? rmwWrite.id with
          | none => state.requests
          | some previousWrite =>
            let otherWrites := state.requests.filter
              λ r => r.isWrite && r.address? == rmwWrite.address? &&
                     r.id != rmwWrite.id && r.id != previousWrite.id
            let systemScope := state.scopes.systemScope
            let ocLookup := state.orderConstraints.lookup systemScope
            let failed := otherWrites.any
              λ wr => ocLookup previousWrite.id wr.id && ocLookup wr.id rmwWrite.id
            let rmwWrite' := if failed then rmwWrite.updateValue none else rmwWrite.validateWrite
            -- update other writes
            let updated := otherWrites.map
              λ wr => match state.rmwGetPreviousWrite? wr.id with
                | none => wr
                | some previousWrite' => if previousWrite'.id == previousWrite.id -- TODO: is this sufficient?
                  then wr.updateValue none -- fail
                  else wr
            updated.foldl RequestArray.insert (state.requests.insert rmwWrite')

def SystemState.satisfy : SystemState → RequestId → RequestId → SystemState
 | state, readId, writeId =>
 let opRead := state.requests.getReq? readId
 let opWrite := state.requests.getReq? writeId
 match opRead, opWrite with
   | some read, some write =>
     let satisfied' := (readId,writeId)::state.satisfied |>.toArray.qsort lexBLe |>.toList
     let read' := read.setValue write.value?
     -- update rmwWrites
     let requests' := state |>.validateWrite writeId |>.remove readId
     let removed' := read'::state.removed |>.toArray.qsort
       (λ r₁ r₂ => Nat.ble r₁.id r₂.id) |>.toList
     let result := { requests := requests', orderConstraints := state.orderConstraints,
                     removed := removed', satisfied := satisfied',
                     threadTypes := state.threadTypes, removedCoherent := sorry
                     : SystemState}
     result.cleanupTransactions
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

