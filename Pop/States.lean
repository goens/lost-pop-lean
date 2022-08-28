import Pop.Util
import Std
import Lean
open Util Std.HashMap

namespace Pop

def RequestId := Nat deriving ToString, BEq, Inhabited, Hashable
def Value := Option Nat deriving ToString, BEq, Inhabited
def Address := Nat deriving ToString, BEq, Inhabited
def ThreadId := Nat deriving BEq, Ord, LT, LE, ToString, Inhabited, Hashable

def RequestId.toNat : RequestId → Nat := λ x => x
def ThreadId.toNat : ThreadId → Nat := λ x => x
def RequestId.ofNat : Nat → RequestId := λ x => x
def ThreadId.ofNat : Nat → RequestId := λ x => x
def Address.ofNat : Nat → Address := λ x => x
def Value.ofNat : Nat → Value := λ x => some x
def Value.ofOptionNat : Option Nat → Value := λ x => x

instance : OfNat ThreadId n where  ofNat := ThreadId.ofNat n
instance : OfNat RequestId n where  ofNat := RequestId.ofNat n
instance : OfNat Address n where ofNat := Address.ofNat n
instance : OfNat Value n where ofNat := Value.ofNat n
instance : Coe RequestId Nat where coe := RequestId.toNat

instance : Lean.Quote ThreadId where quote := λ n => Lean.quote (ThreadId.toNat n)

def Address.prettyPrint (addr : Address) : String :=
  match (OfNat.ofNat addr) with
    | 0 => s!"x"
    | 1 => s!"y"
    | 2 => s!"z"
    | addr => s!"v{addr}"

class ArchReq where
(type : Type 0)
(instBEq : BEq type)
(instInhabited : Inhabited type)
(instToString : ToString type)
(isPermanentRead : type → Bool)

variable [ArchReq]

structure ReadRequest where
 addr : Address
 reads_from : Option RequestId
 val : Value
 deriving BEq

structure WriteRequest where
 addr : Address
 val : Value
 deriving BEq

instance : BEq ArchReq.type := ArchReq.instBEq
instance : Inhabited ArchReq.type := ArchReq.instInhabited
instance : ToString ArchReq.type := ArchReq.instToString

inductive BasicRequest
 | read : ReadRequest → ArchReq.type → BasicRequest
 | write : WriteRequest → ArchReq.type → BasicRequest
 | barrier : ArchReq.type → BasicRequest
 deriving BEq

instance : Inhabited BasicRequest where default := BasicRequest.barrier default

def BasicRequest.toString : BasicRequest → String
  | BasicRequest.read  rr _ => s!"read (Addr{rr.addr}) : {rr.val}"
  | BasicRequest.write  wr _ => s!"write (Addr{wr.addr}) : {wr.val}"
  | BasicRequest.barrier _ => "barrier"

def BasicRequest.prettyPrint : BasicRequest → String
  | BasicRequest.read rr ty =>
    let valStr := match rr.val with
      | none => ""
      | some val => s!"({val})"
    let tyStr := match s!"{ty}" with
      | "" => ""
      | str => s!".{str}"
    s!"R{tyStr} {rr.addr.prettyPrint}{valStr}"
  | BasicRequest.write  wr ty =>
    let valStr := match wr.val with
     | none => ""
     | some val => s!"({val})"
    let tyStr := match s!"{ty}" with
      | "" => ""
      | str => s!".{str}"
    s!"W{tyStr} {wr.addr.prettyPrint}{valStr}"
  | BasicRequest.barrier _ => "Fence"

instance : ToString (BasicRequest) where toString := BasicRequest.toString

def BasicRequest.type : BasicRequest → ArchReq.type
  | BasicRequest.read  _ t => t
  | BasicRequest.write  _ t => t
  | BasicRequest.barrier t => t

def BasicRequest.setValue : (BasicRequest) → Value → (BasicRequest)
  | BasicRequest.read rr rt, v => BasicRequest.read {rr with val := v} rt
  | br@_ , _ => br

def BasicRequest.value? : BasicRequest → Value
  | BasicRequest.read rr _ => rr.val
  | BasicRequest.write wr _ => wr.val
  | _ => none

structure ValidScopes where
  system_scope : List ThreadId
  scopes : ListTree ThreadId

def ValidScopes.default : ValidScopes := { system_scope := [], scopes := ListTree.leaf []}
instance : Inhabited ValidScopes where default := ValidScopes.default

structure Scope {V : ValidScopes} where
  threads : List ThreadId
  valid : threads ∈ V.scopes

instance {V : ValidScopes} : BEq (@Scope V) where
  beq := λ scope₁ scope₂ => scope₁.threads == scope₂.threads

instance {V : ValidScopes} : BEq (@Scope V) where
  beq := λ scope₁ scope₂ => scope₁.threads == scope₂.threads

instance {V : ValidScopes} : LE (@Scope V) where
  le := λ scope₁ scope₂ => List.sublist scope₁.threads scope₂.threads

structure Request where
  id : RequestId
  propagated_to : List ThreadId
  thread : ThreadId
  basic_type : BasicRequest
  -- scope : Scope
  -- type : α
  deriving BEq

def Request.default : Request :=
  {id := 0, propagated_to := [], thread := 0,
   basic_type := BasicRequest.barrier Inhabited.default}
instance : Inhabited (Request) where default := Request.default

def Request.toString : Request → String
  | req => s!" Request {req.id} {req.basic_type.prettyPrint} : [propagated to {req.propagated_to}, origin thread : {req.thread}]"
instance : ToString (Request) where toString := Request.toString

def BasicRequest.isRead    (r : BasicRequest) : Bool := match r with | read  _ _ => true | _ => false
def BasicRequest.isWrite   (r : BasicRequest) : Bool := match r with | write _ _ => true | _ => false
def BasicRequest.isBarrier (r : BasicRequest) : Bool := match r with | barrier _ => true | _ => false
def Request.isRead    (r : Request) : Bool := r.basic_type.isRead
def Request.isWrite   (r : Request) : Bool := r.basic_type.isWrite
def Request.isBarrier (r : Request) : Bool := r.basic_type.isBarrier
def Request.isMem     (r : Request) : Bool := !r.basic_type.isBarrier
def Request.isPermanentRead (r : Request) : Bool := r.isRead && ArchReq.isPermanentRead r.basic_type.type

def Request.value? (r : Request) : Value := r.basic_type.value?
def Request.setValue (r : Request) (v : Value) : Request := { r with basic_type := r.basic_type.setValue v}
def Request.isSatisfied (r : Request) : Bool := match r.basic_type with
  | .read rr _ => rr.val.isSome
  | _ => false

def BasicRequest.address? (r : BasicRequest) : Option Address := match r with
  | read  req _ => some req.addr
  | write req _ => some req.addr
  | _ => none

def Request.address? (r : Request) : Option Address := r.basic_type.address?
def SatisfiedRead := RequestId × RequestId deriving ToString, BEq

def ValidScopes.validate (V : ValidScopes) (threads : List ThreadId) : (@Scope V) :=
 { threads := threads, valid := sorry }

def ValidScopes.subscopes (V : ValidScopes) (S : @Scope V) : List (@Scope V) :=
  let children := V.scopes.children S.threads
  children.map V.validate

def ValidScopes.containThread (V: ValidScopes) (t : ThreadId) : List (@Scope V) :=
  let containing := V.scopes.children [t]
  containing.map V.validate

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

def OrderConstraints.successors {V : ValidScopes} (S : @Scope V) (req : RequestId)
  (reqs : List RequestId) (constraints : @OrderConstraints V)  : List RequestId :=
  let sc_oc := constraints.lookup S -- hope this gets optimized accordingly...
  reqs.filter (λ x => sc_oc req x)

def OrderConstraints.between {V : ValidScopes} (S : @Scope V) (req₁ req₂ : RequestId)
  (reqs : List RequestId) (constraints : @OrderConstraints V)  : List RequestId :=
  let preds₁ := constraints.predecessors S req₁ reqs
  let preds₂ := constraints.predecessors S req₂ reqs
  preds₂.removeAll (req₁::preds₁)

/-
def SystemState.betweenRequests (state : SystemState) (req₁ req₂ : Request) : List Request :=
  let betweenIds := state.orderConstraints.between
    req₁.id req₂.id (reqIds state.requests)
  state.idsToReqs betweenIds
  -/

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

def OrderConstraints.addSingleScope {V : ValidScopes} (constraints : @OrderConstraints V)
  (scope : @Scope V) (reqs : List (RequestId × RequestId)) (val := true) : @OrderConstraints V :=
  match constraints.val.find? scope.threads with
   | none => constraints
   | some sc_oc =>
       let sc_oc' := reqs.foldl (init := sc_oc) λ oc req => oc.insert req val
       let val' := constraints.val.insert scope.threads sc_oc'
       { constraints with val := val' }

def OrderConstraints.addSubscopes {V : ValidScopes} (constraints : @OrderConstraints V)
(scope : @Scope V) (reqs : List (RequestId × RequestId)) (val := true) : @OrderConstraints V :=
  let subscopes := V.subscopes scope
  --dbg_trace s!"{scope.threads}.subscopes: {subscopes.map λ s => s.threads}"
  subscopes.foldl (init := constraints) λ oc sc => oc.addSingleScope sc reqs (val := val)

def OrderConstraints.swap {V : ValidScopes} (oc : @OrderConstraints V)
  (scope : @Scope V) (req₁ req₂ : RequestId) : @OrderConstraints V :=
  let c₁₂ := oc.lookup scope req₁ req₂
  let c₂₁ := oc.lookup scope req₂ req₁
  Id.run do
    if c₁₂ == c₂₁ then
      panic! "cycle {req₁.id} ↔ {req₂.id} detected in order constraints."
    let mut add := []
    let mut remove := []
    if c₁₂ then
      add :=( req₂,req₁) :: add
      remove :=( req₁,req₂) :: remove
    if c₂₁ then
      add :=( req₁,req₂) :: add
      remove :=( req₂,req₁) :: remove
    let mut oc' := oc
    oc' := oc'.addSubscopes scope add
    oc' := oc'.addSubscopes scope remove (val := false)
    return oc'

def OrderConstraints.toString {V : ValidScopes} (constraints : @OrderConstraints V) (scope : @Scope V) (reqs : List RequestId) : String :=
   let reqPairs := List.join $ reqs.map (λ r => reqs.foldl (λ rs' r' => (r,r')::rs') [])
   let reqTrue := reqPairs.filter $ λ (r₁,r₂) => constraints.lookup scope r₁ r₂
   reqTrue.toString

private def opReqId? : Option (Request) → Option RequestId := Option.map λ r => r.id

private def valConsistent (vals :  Array (Option (Request))) : Bool :=
  let valOpIds := vals.map opReqId?
  let valConsistent := λ idx opVal => match opVal with
    | none => true
    | some val => val == idx.val
  let consistentVals := valOpIds.mapIdx valConsistent
  consistentVals.foldl (. && .) true

structure RequestArray where
  val : Array (Option (Request))
  coherent : valConsistent val = true

instance : BEq (RequestArray) where beq := λ arr₁ arr₂ => arr₁.val == arr₂.val

def RequestArray.getReq? : (RequestArray) → RequestId → Option (Request)
  | arr, rId => match arr.val[rId.toNat]? with
    | some (some req) => some req
    | _ => none

def RequestArray.map {β : Type} : RequestArray → (Request → β) → Array β
 | rarr, f => filterNonesArr $ rarr.val.map λ opreq => Option.map f opreq
-- instance : GetElem RequestArray RequestId (Option Request) where getElem

theorem emptyArrayCoherent : valConsistent (Array.mk ([] : List (Option (Request)))) := by
  sorry -- metavariable screws up simp

def RequestArray.empty : RequestArray :=
  { val := Array.mk [], coherent := emptyArrayCoherent }

def RequestArray.toString : RequestArray → String
  | arr => String.intercalate ",\n" $ List.map Request.toString $ filterNones arr.val.toList

instance : ToString (RequestArray) where toString := RequestArray.toString

def RequestArray.filter : RequestArray → (Request → Bool) → List Request
  | ra, f =>
  let fOp : Option Request → Bool
    | some r => f r
    | none => false
  filterNones $ Array.toList $ ra.val.filter fOp

def reqIds : (RequestArray) → List RequestId
 | arr =>
   let opIds :=  Array.toList $ arr.val.map (Option.map Request.id)
   filterNones opIds

def growArray {α : Type} (a : Array (Option α)) (n : Nat) : Array (Option α) :=
  --dbg_trace s!"growing array of size {a.size} by {n}"
  a.append (Array.mkArray (a.size - n) none)

private def RequestArray._insert : RequestArray → Request → Array (Option (Request))
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

def RequestArray.insertAtPosition : RequestArray → Option (Request) → USize → RequestArray
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
  removed : List (Request)
  scopes : ValidScopes
  satisfied : List SatisfiedRead
  orderConstraints : @OrderConstraints scopes
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

instance : BEq (SystemState) where beq := SystemState.beq

def SystemState.oderConstraintsString (state : SystemState)
(scope : optParam (@Scope state.scopes) state.scopes.systemScope) : String :=
  state.orderConstraints.toString scope $ filterNones $ state.requests.val.toList.map $ Option.map Request.id

def SystemState.toString : SystemState → String
  | state => s!"requests:\n{state.requests.toString}\n"  ++
  s!"seen: {state.seen.toString}\n" ++
  s!"removed: {state.removed.toString}\n" ++
  s!"satisfied: {state.satisfied.toString}\n" ++
  s!"constraints: {state.oderConstraintsString}\n"

def SystemState.orderPredecessors (state : SystemState) (scope : @Scope state.scopes)
  (reqId : RequestId) : List RequestId :=
  state.orderConstraints.predecessors scope reqId (reqIds state.requests)

instance : ToString (SystemState) where toString := SystemState.toString

theorem emptyCoherent (requests : RequestArray) :
  ∀ id : RequestId, id ∈ [] → id ∈ reqIds requests := by
  intros id h
  contradiction

theorem empty2Coherent (seen : List RequestId) :
  ∀ id₁ id₂ : RequestId, (id₁,id₂) ∈ [] → id₁ ∈ seen ∧ id₂ ∈ seen := by
  intros
  contradiction

def SystemState.init (S : ValidScopes) : SystemState :=
  { requests := RequestArray.empty, seen := [], removed := [],
    scopes := S, satisfied := [], orderConstraints := OrderConstraints.empty,
    seenCoherent := emptyCoherent RequestArray.empty,
    removedCoherent := emptyCoherent RequestArray.empty,
    satisfiedCoherent := empty2Coherent []
  }

def SystemState.default := SystemState.init ValidScopes.default
instance : Inhabited (SystemState) where default := SystemState.default


def SystemState.threads : SystemState → List ThreadId
 | s => s.scopes.system_scope

def SystemState.idsToReqs : (SystemState) → List RequestId → List (Request)
  | state, ids => filterNones $ ids.map (λ id => state.requests.getReq? id)

def SystemState.isSatisfied : SystemState → RequestId → Bool
  | state, rid =>
  !(state.satisfied.filter λ (srd,_) => srd == rid).isEmpty

def SystemState.reqPropagatedTo : SystemState → RequestId → ThreadId → Bool
  | state, rid, tid => match state.requests.getReq? rid with
    | none => false
    | some req => req.propagatedTo tid

class Arch where
  (req : ArchReq)
  (acceptConstraints : SystemState → BasicRequest → ThreadId → Bool )
  (propagateConstraints : SystemState → RequestId → ThreadId → Bool)
  (satisfyReadConstraints : SystemState → RequestId → RequestId → Bool)
  (reorderCondition : Request → Request → Bool)
  (requestScope : (valid : ValidScopes) → Request → @Scope valid)

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
