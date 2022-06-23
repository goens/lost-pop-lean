namespace POP

def RequestId := Nat deriving ToString, BEq
def Value := Nat deriving ToString, BEq
def Address := Nat deriving ToString, BEq
def ThreadId := Nat deriving BEq, Ord, LT, LE, ToString

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

private def reqIds : List Request → List RequestId := List.map Request.id
theorem reqIds_preserves_cons (r : Request) (reqs : List Request) :
  r.id :: reqIds reqs = reqIds (r::reqs) := by simp [reqIds,List.map]

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

def Request.propagatedTo (r : Request) (t : ThreadId) : Bool := r.propagated_to.elem t

def Request.fullyPropagated {V : ValidScopes}  (r : Request) (s : optParam (@Scope V) V.systemScope) : Bool :=
  let propToList := s.threads.map (λ t => Request.propagatedTo r t)
  propToList.foldl (init:= true) (. && .)

structure System where
  scopes : ValidScopes

def System.threads : System → List ThreadId
 | s => List.join s.scopes.scopes

def OrderConstraints := RequestId → RequestId → Bool
def OrderConstraints.predecessors (req : RequestId) (reqs : List RequestId)
  (constraints : OrderConstraints)  : List RequestId :=
  reqs.filter (λ x => constraints x req)

structure SystemState where
  requests : List Request
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

theorem acceptingPreservesCoherence {req : Request} {reqs₁ : List RequestId} (reqs₂ : List Request)
    (h : ∀ id : RequestId, id ∈ reqs₁ → id ∈ reqIds reqs₂) :
    ∀ id : RequestId, id ∈ reqs₁ → id ∈ reqIds (req :: reqs₂) := by
    intro r h'
    have r_in_reqs₂ := h r h'
    rewrite [← reqIds_preserves_cons req reqs₂]
    exact List.Mem.tail (Request.id req) r_in_reqs₂

def SystemState.acceptRequest : SystemState → BasicRequest → ThreadId → SystemState
  | state, reqType, tId =>
  let req : Request := { propagated_to := [tId], thread := tId, basic_type := reqType}
  let requests' := req :: state.requests
  { requests := requests', system := state.system, seen := state.seen,
    orderConstraints := state.orderConstraints,
    removed := state.removed, satisfied := state.satisfied,
    seenCoherent := acceptingPreservesCoherence state.requests state.seenCoherent,
    removedCoherent := @acceptingPreservesCoherence req state.removed state.requests state.removedCoherent,
    satisfiedCoherent := state.satisfiedCoherent
  }

def SystemState.propagated? : SystemState → RequestId → ThreadId → Bool
 | state, reqId, thId =>
   let queryRequest := λ req =>
     if req.id == reqId
     then req.propagated_to.elem thId
     else false
   let maps := state.requests.map queryRequest
   maps.foldl (. || .) false

def SystemState.canPropagate : SystemState → RequestId → ThreadId → Bool
 | state, reqId, thId =>
   let unpropagated := state.propagated? reqId thId
   let order_constraints := state.orderConstraints state.system.scopes.systemScope
   let pred := OrderConstraints.predecessors reqId (reqIds state.requests) order_constraints
   let reqs := state.requests.filter (λ req => pred.elem req.id)
   let predPropagated := reqs.map (λ r => r.fullyPropagated state.system.scopes.systemScope)
   unpropagated || predPropagated.foldl (. && .) true

def SystemState.propagate : SystemState → RequestId → ThreadId → SystemState := sorry
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
