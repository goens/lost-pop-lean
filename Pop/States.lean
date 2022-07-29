import Pop.Util
import Std
open Util Std.HashMap

namespace Pop

def RequestId := Nat deriving ToString, BEq, Inhabited, Hashable
def Value := Option Nat deriving ToString, BEq, Inhabited
def Address := Nat deriving ToString, BEq, Inhabited
def ThreadId := Nat deriving BEq, Ord, LT, LE, ToString, Inhabited, Hashable

def RequestId.toNat : RequestId → Nat := λ x => x
def ThreadId.toNat : RequestId → Nat := λ x => x
def RequestId.ofNat : Nat → RequestId := λ x => x
def ThreadId.ofNat : Nat → RequestId := λ x => x
def Address.ofNat : Nat → Address := λ x => x
def Value.ofNat : Nat → Value := λ x => some x

instance : OfNat ThreadId n where  ofNat := ThreadId.ofNat n
instance : OfNat RequestId n where  ofNat := RequestId.ofNat n
instance : OfNat Address n where ofNat := Address.ofNat n
instance : OfNat Value n where ofNat := Value.ofNat n
instance : Coe RequestId Nat where coe := RequestId.toNat

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

instance : Inhabited BasicRequest where default := BasicRequest.barrier

def mkRead (addr : Address) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  BasicRequest.read rr

def mkWrite (addr : Address) (val : Value) : BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := val}
  BasicRequest.write wr

def mkBarrier : BasicRequest := BasicRequest.barrier

def BasicRequest.toString
  | BasicRequest.read  rr => s!"read (Addr{rr.addr}) : {rr.val}"
  | BasicRequest.write  wr => s!"write (Addr{wr.addr}) : {wr.val}"
  | BasicRequest.barrier => "barrier"
instance : ToString BasicRequest where toString := BasicRequest.toString

def BasicRequest.setValue : BasicRequest → Value → BasicRequest
  | BasicRequest.read rr, v => BasicRequest.read {rr with val := v}
  | br@_ , _ => br

def BasicRequest.value? : BasicRequest → Value
  | BasicRequest.read rr => rr.val
  | BasicRequest.write wr => wr.val
  | _ => none

structure ValidScopes where
  system_scope : List ThreadId
  scopes : ListTree ThreadId system_scope

def ValidScopes.default : ValidScopes := { system_scope := [], scopes := ListTree.leaf []}
instance : Inhabited ValidScopes where default := ValidScopes.default

structure Scope {V : ValidScopes} where
  threads : List ThreadId
  valid : threads ∈ V.scopes


structure Request where
  id : RequestId
  propagated_to : List ThreadId
  thread : ThreadId
  basic_type : BasicRequest
  -- scope : Scope
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

def Request.value? (r : Request ) : Value := r.basic_type.value?
def Request.setValue (r : Request ) (v : Value) : Request := { r with basic_type := r.basic_type.setValue v}

def BasicRequest.address? (r : BasicRequest) : Option Address := match r with
  | read  req => some req.addr
  | write req => some req.addr
  | _ => none

def Request.address? (r : Request) : Option Address := r.basic_type.address?

def SatisfiedRead := RequestId × RequestId deriving ToString, BEq

def ValidScopes.validate (V : ValidScopes) (threads : List ThreadId) : (@Scope V) :=
 { threads := threads, valid := sorry }

def ValidScopes.subscopes (V : ValidScopes) (S : @Scope V) : List (@Scope V) :=
  let children := V.scopes.children S.threads
  children.map V.validate

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

def System.requestScope (sys : System) (req : Request) : @Scope sys.scopes :=
  sys.scopes.systemScope -- TODO: change here for scoped version

theorem sameOrderConstraints {system₁ system₂ : System} :
  system₁ = system₂ → system₁.scopes = system₂.scopes := by
  intros h
  rw [h]

/-
 We have scoped order constraints, i.e. a different set of order constraints
 for each scope. Order constraints specify a partial order on requests, and
 we represent them with a Bool value for a pair of (r₁,r₂) : RequestId × RequestId,
 which is true ↔ there is an order constraint r₁ →s r₂, for the scope s.

 However, we have a property (by construction) that if s' ≤ s and r₁ →s r₂, then
 also r₁ →s' r₂. Can we use this to find a more compact representation?
-/
structure OrderConstraints {V : ValidScopes} where
  val : Std.HashMap (List ThreadId) (Std.HashMap (RequestId × RequestId) Bool)
  default : Bool

def OrderConstraints.empty {V : ValidScopes} (numReqs : optParam Nat 10) : @OrderConstraints V :=
 let scopes := V.scopes.toList
 { default := false, val :=
 Std.mkHashMap (capacity := scopes.length) |> scopes.foldl λ acc s => acc.insert s (Std.mkHashMap (capacity := numReqs))
 }

def OrderConstraints.lookup {V : ValidScopes} (ordc : @OrderConstraints V)
  (S : @Scope V) (req₁ req₂ : RequestId) : Bool :=
  let sc_ordc := ordc.val.find? S.threads
  match sc_ordc with
    | none => ordc.default
    | some hashmap =>
      hashmap.findD (req₁, req₂) ordc.default

def OrderConstraints.predecessors {V : ValidScopes} (S : @Scope V) (req : RequestId)
    (reqs : List RequestId) (constraints : @OrderConstraints V)  : List RequestId :=
    let sc_oc := constraints.lookup S -- hope this gets optimized accordingly...
    reqs.filter (λ x => sc_oc x req)

def OrderConstraints.between {V : ValidScopes} (S : @Scope V) (req₁ req₂ : RequestId)
  (reqs : List RequestId) (constraints : @OrderConstraints V)  : List RequestId :=
  let preds₁ := constraints.predecessors S req₁ reqs
  let preds₂ := constraints.predecessors S req₂ reqs
  preds₂.removeAll (req₁::preds₁)

def OrderConstraints.compare {V₁ V₂ : ValidScopes} ( oc₁ : @OrderConstraints V₁) (oc₂ : @OrderConstraints V₂)
  (requests : List RequestId) : Bool :=
  if V₁.scopes.toList != V₂.scopes.toList
    then false
    else
      let scopes₁ := V₁.scopes.toList.map V₁.validate
      let scopes₂ := V₂.scopes.toList.map V₂.validate
      let scopes := scopes₁.zip scopes₂ -- pretty hacky: should get types to match
      let reqPairs := List.join $ requests.map λ r₁ => requests.foldl (init := []) λ reqs r₂ => (r₁,r₂)::reqs
      let keys := List.join $ scopes.map λ s => reqPairs.foldl (init := []) λ ks (r₁,r₂) => (s,r₁,r₂)::ks
      keys.all λ (s,r₁,r₂) => (oc₁.lookup s.1 r₁ r₂ == oc₂.lookup s.2 r₁ r₂)

-- Maybe I don't need this (at least for now)
/-
def OrderConstraints.purgeScope {V : ValidScopes} (constraints : @OrderConstraints V)
  (scope : @Scope V) (req : RequestId) : @OrderConstraints V :=
match constraints.val.find? V.system_scope with
| none => constraints
| some ss_oc =>
let allReqPairs := ss_oc.toArray.map λ (pair,_) => pair
let reqPairs := allReqPairs.filter λ (r₁, r₂) => r₁ == req || r₂ == req
let val' := constraints.val.toArray.foldl λ scope sc_oc => Id.run do
let sc_oc' := reqPairs.foldl (init := sc_oc) λ oc reqs => oc.insert reqs false
return sc_oc'
{ constraints with val := val'}

def OrderConstraints.purge {V : ValidScopes} (constraints : @OrderConstraints V)
  (req : RequestId) : @OrderConstraints V :=
  match constraints.val.find? V.system_scope with
    | none => constraints
    | some ss_oc =>
      let allReqPairs := ss_oc.toArray.map λ (pair,_) => pair
      let reqPairs := allReqPairs.filter λ (r₁, r₂) => r₁ == req || r₂ == req
      let val' := constraints.val.toArray.foldl λ scope sc_oc => Id.run do
        let sc_oc' := reqPairs.foldl (init := sc_oc) λ oc reqs => oc.insert reqs false
        return sc_oc'
      { constraints with val := val'}
-/

def OrderConstraints.add_single_scope {V : ValidScopes} (constraints : @OrderConstraints V)
  (scope : @Scope V) (reqs : List (RequestId × RequestId)) : @OrderConstraints V :=
  match constraints.val.find? scope.threads with
   | none => constraints
   | some sc_oc =>
       let sc_oc' := reqs.foldl (init := sc_oc) λ oc req => oc.insert req true
       let val' := constraints.val.insert scope.threads sc_oc'
       { constraints with val := val' }

def OrderConstraints.add_subscopes {V : ValidScopes} (constraints : @OrderConstraints V)
(scope : @Scope V) (reqs : List (RequestId × RequestId)) : @OrderConstraints V :=
  let subscopes := V.subscopes scope
  --dbg_trace s!"{scope.threads}.subscopes: {subscopes.map λ s => s.threads}"
  subscopes.foldl (init := constraints) λ oc sc => oc.add_single_scope sc reqs

def OrderConstraints.toString {V : ValidScopes} (constraints : @OrderConstraints V) (scope : @Scope V) (reqs : List RequestId) : String :=
   let reqPairs := List.join $ reqs.map (λ r => reqs.foldl (λ rs' r' => (r,r')::rs') [])
   let reqTrue := reqPairs.filter $ λ (r₁,r₂) => constraints.lookup scope r₁ r₂
   reqTrue.toString

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

def RequestArray.getReq? : RequestArray → RequestId → Option Request
  | arr, rId => match arr.val[rId.toNat]? with
    | some (some req) => some req
    | _ => none

-- instance : GetElem RequestArray RequestId (Option Request) where getElem

instance : BEq RequestArray where beq := λ r₁ r₂ => r₁.val == r₂.val

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
  --dbg_trace s!"growing array of size {a.size} by {n}"
  a.append (Array.mkArray (a.size - n) none)

private def RequestArray._insert : RequestArray → Request → Array (Option Request)
  | arr, req =>
    --dbg_trace "growing [{arr}] of size {arr.val.size} to {req.id.toNat + 1} for Request {req}"
    let vals' := growArray arr.val (req.id.toNat + 1)
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

def RequestArray.insertAtPosition : RequestArray → Option Request → USize → RequestArray
  | arr, opReq, i =>
    let val' := if h : i.toNat < arr.val.size
      then arr.val.uset i opReq h
      else match opReq with
        | some req => arr._insert req
        | none => arr.val
      -- RequestArrayInsertConsistent arr req
    { val := val', coherent := sorry}

def RequestArray.insert : RequestArray → Request → RequestArray
  | arr, req =>
    let i := req.id.toNat.toUSize
    arr.insertAtPosition (some req) i

def RequestArray.remove : RequestArray → RequestId → RequestArray
  | arr, reqId =>
  match arr.getReq? reqId with
    | none => arr
    | some req =>
      let i := req.id.toNat.toUSize
      arr.insertAtPosition none i

structure SystemState where
  requests : RequestArray
  seen : List RequestId
  removed : List Request
  system : System
  satisfied : List SatisfiedRead
  orderConstraints : @OrderConstraints system.scopes
  seenCoherent : ∀ id : RequestId, id ∈ seen → id ∈ reqIds requests
  removedCoherent : ∀ id : RequestId, id ∈ (removed.map Request.id) → id ∈ reqIds requests
  satisfiedCoherent : ∀ id₁ id₂ : RequestId, (id₁,id₂) ∈ satisfied → id₁ ∈ seen ∧ id₂ ∈ seen

def SystemState.beq (state₁ state₂ : SystemState)
  -- (samesystem : state₁.system = state₂.system)
  : Bool :=
  state₁.requests == state₂.requests &&
  state₁.seen == state₂.seen &&
  state₁.removed == state₂.removed &&
  state₁.satisfied == state₂.satisfied &&
  -- this will be expensive!
  state₁.orderConstraints.compare state₂.orderConstraints (reqIds state₁.requests)

instance : BEq SystemState where beq := SystemState.beq

def SystemState.oderConstraintsString (state : SystemState) (scope : optParam (@Scope state.system.scopes) state.system.scopes.systemScope) : String :=
  state.orderConstraints.toString scope $ filterNones $ state.requests.val.toList.map $ Option.map Request.id

def SystemState.toString : SystemState → String
  | state => s!"requests:\n{state.requests.toString}\n"  ++
  s!"seen: {state.seen.toString}\n" ++
  s!"removed: {state.removed.toString}\n" ++
  s!"satisfied: {state.satisfied.toString}\n" ++
  s!"constraints: {state.oderConstraintsString}\n"

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
  | state, ids => filterNones $ ids.map (λ id => state.requests.getReq? id)

def SystemState.isSatisfied : SystemState → RequestId → Bool
  | state, rid => !(state.satisfied.filter λ (srd,_) => srd == rid).isEmpty

def SystemState.reqPropagatedTo : SystemState → RequestId → ThreadId → Bool
  | state, rid, tid => match state.requests.getReq? rid with
    | none => false
    | some req => req.propagatedTo tid

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
