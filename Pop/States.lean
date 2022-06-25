namespace POP

def RequestId := Nat deriving ToString, BEq
def Value := Nat deriving ToString, BEq
def Address := Nat deriving ToString, BEq
def ThreadId := Nat deriving BEq, Ord, LT, LE, ToString

def RequestId.toNat : RequestId → Nat := λ x => x

structure ReadRequest where
 addr : Address
 reads_from : RequestId
 val : Value

structure WriteRequest where
 addr : Address
 val : Value

inductive BasicRequest
 | read : ReadRequest → BasicRequest
 | write : WriteRequest → BasicRequest
 | barrier : BasicRequest

-- TODO: write properly
def BasicRequest.toString
  | BasicRequest.read  _ => "read"
  | BasicRequest.write _ => "write"
  | BasicRequest.barrier => "barrier"
instance : ToString BasicRequest where toString := BasicRequest.toString

structure Request where
  id : RequestId
  propagated_to : List ThreadId
  thread : ThreadId
  basic_type : BasicRequest
  -- type : α

def BasicRequest.isRead    (r : BasicRequest) : Bool := match r with | read  _ => true | _ => false
def BasicRequest.isWrite   (r : BasicRequest) : Bool := match r with | write _ => true | _ => false
def BasicRequest.isBarrier (r : BasicRequest) : Bool := match r with | barrier => true | _ => false
def Request.isRead    (r : Request) : Bool := r.basic_type.isRead
def Request.isWrite   (r : Request) : Bool := r.basic_type.isWrite
def Request.isBarrier (r : Request) : Bool := r.basic_type.isBarrier

def BasicRequest.address? (r : BasicRequest) : Option Address := match r with
  | read  req => some req.addr
  | write req => some req.addr
  | _ => none

def Request.address? (r : Request) : Option Address := r.basic_type.address?

def SatisfiedRead := RequestId × RequestId deriving ToString

structure ValidScopes where
  scopes : List (List ThreadId)
  threads_in : ∀ n : ThreadId, n ∈ List.join scopes → [n] ∈ scopes
  system_in : List.join scopes ∈ scopes

structure Scope {V : ValidScopes} where
  threads : List ThreadId
  valid : threads ∈ V.scopes

def ValidScopes.systemScope {V : ValidScopes } : @Scope V :=
  {threads := List.join V.scopes, valid := V.system_in}

def ValidScopes.threadScope {V : ValidScopes } (t :  ThreadId) (h : [t] ∈ V.scopes) : (@Scope V) :=
  {threads := [t], valid := h}

def ValidScopes.jointScope : (V : ValidScopes) → ThreadId → ThreadId → (@Scope V) := sorry

def Request.propagatedTo (r : Request) (t : ThreadId) : Bool := r.propagated_to.elem t

def Request.fullyPropagated {V : ValidScopes}  (r : Request) (s : optParam (@Scope V) V.systemScope) : Bool :=
  let propToList := s.threads.map (λ t => Request.propagatedTo r t)
  propToList.foldl (init:= true) (. && .)

structure System where
  scopes : ValidScopes

def System.threads : System → List ThreadId
 | s => List.join s.scopes.scopes

def OrderConstraints {V : ValidScopes} :=  (@Scope V) → RequestId → RequestId → Bool

def OrderConstraints.predecessors {V : ValidScopes} (S : @Scope V) (req : RequestId)
    (reqs : List RequestId) (constraints : @OrderConstraints V)  : List RequestId :=
    reqs.filter (λ x => constraints S x req)

def OrderConstraints.between {V : ValidScopes} (S : @Scope V) (req₁ req₂ : RequestId)
  (reqs : List RequestId) (constraints : @OrderConstraints V)  : List RequestId :=
  sorry --reqs.filter (λ x => constraints S x req)

def OrderConstraints.purge {V : ValidScopes} (constraints : @OrderConstraints V)
  (req : RequestId) : @OrderConstraints V :=
  λ scope r₁ r₂ =>
    if r₁ == req || r₂ == req
    then false
    else constraints scope r₁ r₂

def OrderConstraints.update {V : ValidScopes} : @OrderConstraints V → RequestId → ThreadId → @OrderConstraints V := sorry

private def opReqId? : Option Request → Option RequestId := Option.map λ r => r.id

private def valConsistent (vals :  Array (Option Request)) : Bool :=
  let valOpIds := vals.map opReqId?
  let valConsistent := λ idx opVal => match opVal with
    | none => true
    | some val => val == idx.val
  let consistentVals := valOpIds.mapIdx valConsistent
  consistentVals.foldl (. && .) true

structure RequestArray where
  val : Array (Option Request)
  coherent : valConsistent val = true

def filterNones {α : Type} : List (Option α) → List α
  | none::rest => filterNones rest
  | (some val):: rest => val::(filterNones rest)
  | [] => []

private def reqIds : RequestArray → List RequestId
 | arr =>
   let opIds :=  Array.toList $ arr.val.map (Option.map Request.id)
   filterNones opIds

def growArray {α : Type} (a : Array (Option α)) (n : Nat) : Array (Option α) :=
  a.append (Array.mkArray (a.size - n) none)

private def RequestArray._insert : RequestArray → Request → Array (Option Request)
  | arr, req =>
    let vals' := growArray arr.val (arr.val.size - req.id.toNat)
    arr.val.insertAt req.id (some req)

-- can't be proving these things right now
theorem RequestArrayInsertConsistent (arr : RequestArray) (req : Request) :
  valConsistent (arr._insert req) = true := by sorry
  -- unfold RequestArray._insert
  -- simp

def RequestArray._remove : RequestArray → RequestId → Array (Option Request)
 | arr, reqId => arr.val.insertAt reqId none

-- should be pretty trivial
theorem RequestArrayRemoveConsistent (arr : RequestArray) (reqId : RequestId) :
  valConsistent (arr._remove reqId) = true := by sorry
--  unfold RequestArray._remove
--  unfold valConsistent

def RequestArray.insert : RequestArray → Request → RequestArray
  | arr, req => { val := arr._insert req, coherent := RequestArrayInsertConsistent arr req}

def RequestArray.remove : RequestArray → RequestId → RequestArray
| arr, reqId => { val := arr._remove reqId , coherent := RequestArrayRemoveConsistent arr reqId}

structure SystemState where
  requests : RequestArray
  seen : List RequestId
  removed : List RequestId
  system : System
  satisfied : List SatisfiedRead
  orderConstraints : @OrderConstraints system.scopes
  seenCoherent : ∀ id : RequestId, id ∈ seen → id ∈ reqIds requests
  removedCoherent : ∀ id : RequestId, id ∈ removed → id ∈ reqIds requests
  satisfiedCoherent : ∀ id₁ id₂ : RequestId, (id₁,id₂) ∈ satisfied → id₁ ∈ seen ∧ id₂ ∈ seen

inductive Transition
  | acceptRequest : BasicRequest → ThreadId → Transition
  | propagateToThread : RequestId → ThreadId → Transition
  | satisfyRead : RequestId → RequestId → Transition

def SystemState.idsToReqs : SystemState → List RequestId → List Request
  | state, ids => filterNones $ ids.map (λ id => state.requests.val[id])

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
    let orderConstraints' := state.orderConstraints.update reqId thId
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

-- private def maxThread : ThreadId → List ThreadId → ThreadId
--   | curmax, n::rest => if curmax < n then maxThread n rest else maxThread curmax rest
--   | max, [] => max

-- def Scopes.numThreads : ValidScopes → ThreadId :=
--   let helperFun : ThreadId → List (List ThreadId) → ThreadId :=
--     λ cmax rest => match rest with
--       | l
-- def Scopes.valid : Scopes → List ThreadId → Boolean :=

-- def Scope.subscopes : Scope → List Scope
--  |


-- def Scope.isSubscrope : Scope → Scope → Boolean :=
-- instance : LE Scope
