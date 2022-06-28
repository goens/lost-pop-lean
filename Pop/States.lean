import Pop.Util
open Util

namespace Pop

def RequestId := Nat deriving ToString, BEq
def Value := Option Nat deriving ToString, BEq
def Address := Nat deriving ToString, BEq
def ThreadId := Nat deriving BEq, Ord, LT, LE, ToString

def RequestId.toNat : RequestId → Nat := λ x => x
def ThreadId.toNat : RequestId → Nat := λ x => x
def RequestId.ofNat : Nat → RequestId := λ x => x
def ThreadId.ofNat : Nat → RequestId := λ x => x
def Address.ofNat : Nat → Address := λ x => x

instance : OfNat ThreadId n where  ofNat := ThreadId.ofNat n
instance : OfNat RequestId n where  ofNat := RequestId.ofNat n
instance : OfNat Address n where ofNat := Address.ofNat n

structure ReadRequest where
 addr : Address
 reads_from : Option RequestId
 val : Value
 deriving BEq

structure WriteRequest where
 addr : Address
 val : Value
 deriving BEq

inductive BasicRequest
 | read : ReadRequest → BasicRequest
 | write : WriteRequest → BasicRequest
 | barrier : BasicRequest
 deriving BEq

def mkRead (addr : Address) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  BasicRequest.read rr

def mkWrite (addr : Address) : BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := none}
  BasicRequest.write wr

def mkBarrier : BasicRequest := BasicRequest.barrier

def BasicRequest.toString
  | BasicRequest.read  rr => s!"read (Addr{rr.addr})"
  | BasicRequest.write  wr => s!"write (Addr{wr.addr})"
  | BasicRequest.barrier => "barrier"
instance : ToString BasicRequest where toString := BasicRequest.toString

structure Request where
  id : RequestId
  propagated_to : List ThreadId
  thread : ThreadId
  basic_type : BasicRequest
  -- type : α
  deriving BEq

def Request.default : Request := {id := 0, propagated_to := [], thread := 0, basic_type := BasicRequest.barrier}
instance : Inhabited Request where default := Request.default

def Request.toString : Request → String
  | req => s!" Request {req.id} {req.basic_type} : [propagated to {req.propagated_to}, origin thread : {req.thread}]"
instance : ToString Request where toString := Request.toString

def BasicRequest.isRead    (r : BasicRequest) : Bool := match r with | read  _ => true | _ => false
def BasicRequest.isWrite   (r : BasicRequest) : Bool := match r with | write _ => true | _ => false
def BasicRequest.isBarrier (r : BasicRequest) : Bool := match r with | barrier => true | _ => false
def Request.isRead    (r : Request) : Bool := r.basic_type.isRead
def Request.isWrite   (r : Request) : Bool := r.basic_type.isWrite
def Request.isBarrier (r : Request) : Bool := r.basic_type.isBarrier
def Request.isMem     (r : Request) : Bool := !r.basic_type.isBarrier

def BasicRequest.address? (r : BasicRequest) : Option Address := match r with
  | read  req => some req.addr
  | write req => some req.addr
  | _ => none

def Request.address? (r : Request) : Option Address := r.basic_type.address?

def SatisfiedRead := RequestId × RequestId deriving ToString

structure ValidScopes where
  system_scope : List ThreadId
  scopes : ListTree ThreadId system_scope
  threads_in : ∀ n : ThreadId, n ∈ system_scope → [n] ∈ scopes

theorem empty_threads_in : ∀ n : ThreadId, n ∈ [] → [n] ∈ ListTree.leaf [] := by
  intros
  contradiction
def ValidScopes.default : ValidScopes := { system_scope := [], scopes := ListTree.leaf [], threads_in := empty_threads_in}
instance : Inhabited ValidScopes where default := ValidScopes.default

structure Scope {V : ValidScopes} where
  threads : List ThreadId
  valid : threads ∈ V.scopes

instance {V : ValidScopes} : Inhabited (@Scope V) where
 default := {threads := [], valid := sorry}

def ValidScopes.systemScope {V : ValidScopes } : @Scope V :=
  {threads := V.system_scope, valid := sorry}

def ValidScopes.threadScope {V : ValidScopes } (t :  ThreadId) (h : [t] ∈ V.scopes) : (@Scope V) :=
  {threads := [t], valid := h}

def ValidScopes.jointScope : (V : ValidScopes) → ThreadId → ThreadId → (@Scope V)
 | valid, t₁, t₂ => match valid.scopes.meet t₁ t₂ with
   | some scope => {threads := scope, valid := sorry}
   | none => unreachable! -- can we get rid of this case distinction?

def Request.propagatedTo (r : Request) (t : ThreadId) : Bool := r.propagated_to.elem t

def Request.fullyPropagated {V : ValidScopes}  (r : Request) (s : optParam (@Scope V) V.systemScope) : Bool :=
  let propToList := s.threads.map (λ t => Request.propagatedTo r t)
  propToList.foldl (init:= true) (. && .)

structure System where
  scopes : ValidScopes
  reorder_condition : Request → Request → Bool

def System.default : System := { scopes := ValidScopes.default, reorder_condition :=  (λ _ _ => false)}
instance : Inhabited System where default := System.default

def System.threads : System → List ThreadId
 | s => s.scopes.system_scope

def OrderConstraints {V : ValidScopes} :=  (@Scope V) → RequestId → RequestId → Bool

def OrderConstraints.empty {V : ValidScopes}  : @OrderConstraints V := λ _ _ _ => false

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


def OrderConstraints.append {V : ValidScopes} (constraints : @OrderConstraints V)
  (scope : @Scope V) (reqs : List (RequestId × RequestId)) : @OrderConstraints V
  | s, r₁, r₂ => if List.sublist s.threads scope.threads && reqs.elem (r₁, r₂)
  then true
  else constraints s r₁ r₂

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

theorem emptyArrayCoherent : valConsistent (Array.mk []) := by simp
def RequestArray.empty : RequestArray :=
  { val := Array.mk [], coherent := emptyArrayCoherent }

def RequestArray.toString : RequestArray → String
  | arr => String.intercalate ",\n" $ List.map Request.toString $ filterNones arr.val.toList
instance : ToString RequestArray where toString := RequestArray.toString

def reqIds : RequestArray → List RequestId
 | arr =>
   let opIds :=  Array.toList $ arr.val.map (Option.map Request.id)
   filterNones opIds

def growArray {α : Type} (a : Array (Option α)) (n : Nat) : Array (Option α) :=
  a.append (Array.mkArray (a.size - n) none)

private def RequestArray._insert : RequestArray → Request → Array (Option Request)
  | arr, req =>
    let vals' := growArray arr.val req.id.toNat
    let i := req.id.toNat.toUSize
    if h : i.toNat < vals'.size
    then vals'.uset i (some req) h
    else if i.toNat == vals'.size
    then vals'.insertAt req.id (some req)
    else unreachable! -- because of growArray before

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

def SystemState.toString : SystemState → String
  | state => s!"requests:\n{state.requests.toString}\n"  ++
  s!"seen: {state.seen.toString}\n" ++
  s!"removed: {state.removed.toString}\n" ++
  s!"satisfied: {state.satisfied.toString}\n"

instance : ToString SystemState where toString := SystemState.toString

theorem emptyCoherent (requests : RequestArray) :
  ∀ id : RequestId, id ∈ [] → id ∈ reqIds requests := by
  intros id h
  contradiction

theorem empty2Coherent (seen : List RequestId) :
  ∀ id₁ id₂ : RequestId, (id₁,id₂) ∈ [] → id₁ ∈ seen ∧ id₂ ∈ seen := by
  intros
  contradiction

def SystemState.init (S : System) : SystemState :=
  { requests := RequestArray.empty, seen := [], removed := [],
    system := S, satisfied := [], orderConstraints := OrderConstraints.empty,
    seenCoherent := emptyCoherent RequestArray.empty,
    removedCoherent := emptyCoherent RequestArray.empty,
    satisfiedCoherent := empty2Coherent []
  }

def SystemState.default := SystemState.init System.default
instance : Inhabited SystemState where default := SystemState.default

def SystemState.idsToReqs : SystemState → List RequestId → List Request
  | state, ids => filterNones $ ids.map (λ id => state.requests.val[id])

def SystemState.isSatisfied : SystemState → RequestId → Bool
  | state, rid => !(state.satisfied.filter λ (srd,_) => srd == rid).isEmpty

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

end Pop
