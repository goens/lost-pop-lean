namespace POP

def RequestId := Nat deriving ToString, BEq
def Value := Nat deriving ToString, BEq
def Address := Nat deriving ToString, BEq
def ThreadId := Nat deriving BEq, Ord, LT, LE, ToString

def RequestId.toNat : RequestId → Nat := λ x => x

structure ReadRequest where
 id : RequestId
 addr : Address
 reads_from : RequestId
 val : Value

structure WriteRequest where
 id : RequestId
 addr : Address
 val : Value

inductive BasicRequest
 | read : ReadRequest → BasicRequest
 | write : WriteRequest → BasicRequest
 | barrier : RequestId → BasicRequest

-- TODO: write properly
def BasicRequest.toString
  | BasicRequest.read _ => "read"
  | BasicRequest.write _ => "write"
  | BasicRequest.barrier _ => "barrier"
instance : ToString BasicRequest where toString := BasicRequest.toString

structure Request where
  propagated_to : List ThreadId
  thread : ThreadId
  basic_type : BasicRequest
  -- type : α

def Request.id (req : Request) : RequestId :=
 match req.basic_type with
  | BasicRequest.read r => r.id
  | BasicRequest.write w => w.id
  | BasicRequest.barrier id => id

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

def RequestArray.insert : RequestArray → Request → RequestArray
  | arr, req => { val := arr._insert req, coherent := RequestArrayInsertConsistent arr req}

structure SystemState where
  requests : RequestArray
  seen : List RequestId
  removed : List RequestId
  system : System
  satisfied : List SatisfiedRead
  orderConstraints : (@Scope system.scopes) → RequestId → RequestId → Bool
  seenCoherent : ∀ id : RequestId, id ∈ seen → id ∈ reqIds requests
  removedCoherent : ∀ id : RequestId, id ∈ removed → id ∈ reqIds requests
  satisfiedCoherent : ∀ id₁ id₂ : RequestId, (id₁,id₂) ∈ satisfied → id₁ ∈ seen ∧ id₂ ∈ seen

inductive Transition
  | acceptRequest : BasicRequest → ThreadId → Transition
  | propagateToThread : RequestId → ThreadId → Transition
  | satisfyRead : RequestId → RequestId → Transition

-- this simple model it can always accept requests
def SystemState.canAcceptRequest : SystemState → BasicRequest → ThreadId → Bool
 | _, _, _ => true

def SystemState.acceptRequest : SystemState → BasicRequest → ThreadId → SystemState
  | state, reqType, tId =>
  let req : Request := { propagated_to := [tId], thread := tId, basic_type := reqType}
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
    let order_constraints : OrderConstraints := state.orderConstraints
    let pred := order_constraints.predecessors scope reqId (reqIds state.requests)
    let reqOps := state.requests.val.filter (λ req => match req with | none => false | some r => pred.elem r.id)
    let reqs := filterNones reqOps.toList
    let predPropagated := reqs.map (λ r => r.fullyPropagated state.system.scopes.systemScope)
    unpropagated || predPropagated.foldl (. && .) true

def Request.propagate : Request → ThreadId → Request
  | req, thId => { req with propagated_to := thId :: req.propagated_to}

def OrderConstraints.update {V : ValidScopes} : @OrderConstraints V → RequestId → ThreadId → @OrderConstraints V := sorry

def SystemState.propagate : SystemState → RequestId → ThreadId → SystemState
  | state, reqId, thId =>
  let reqOpt := state.requests.val[reqId]
  match reqOpt with
  | none => state
  | some req =>
    let requests' := state.requests.insert (req.propagate thId)
    let scope := state.system.scopes.jointScope thId req.thread
    let orderConstraints : OrderConstraints := state.orderConstraints
    let orderConstraints' := orderConstraints.update reqId thId
    { requests := requests', orderConstraints := orderConstraints',
      seen := state.seen, removed := state.removed, satisfied := state.satisfied,
      seenCoherent := sorry, removedCoherent := sorry,
      satisfiedCoherent := state.satisfiedCoherent
    }

def SystemState.canSatisfyRead : SystemState → RequestId → RequestId → Bool := sorry
def SystemState.satisfy : SystemState → RequestId → RequestId → SystemState := sorry

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
