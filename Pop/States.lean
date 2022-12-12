import Pop.Util
open Util Std.HashMap

namespace Pop

def RequestId := Nat deriving ToString, BEq, Inhabited, Hashable
def Value := Option Nat deriving ToString, BEq, Inhabited
def Address := Nat deriving ToString, BEq, Inhabited
def ThreadId := Nat deriving Ord, LT, LE, ToString, Inhabited, Hashable, DecidableEq
inductive ConditionalValue
  | const : Nat → ConditionalValue
  --| transaction : Nat → ConditionalValue
  | addOne : ConditionalValue
  | failed : ConditionalValue
  deriving BEq, Inhabited

def updateConditionalValue : ConditionalValue → Value → ConditionalValue
  | c@(.const _), _ => c
  | .failed , _ => .failed
  | .addOne, some v => .const (v + 1)
  | .addOne, none => .failed

def RequestId.toNat : RequestId → Nat := λ x => x
def ThreadId.toNat : ThreadId → Nat := λ x => x
def RequestId.ofNat : Nat → RequestId := λ x => x
def ThreadId.ofNat : Nat → ThreadId := λ x => x
def Address.ofNat : Nat → Address := λ x => x
def Value.ofNat : Nat → Value := λ x => some x
def Value.ofOptionNat : Option Nat → Value := λ x => x

instance : OfNat ThreadId n where  ofNat := ThreadId.ofNat n
instance : OfNat RequestId n where  ofNat := RequestId.ofNat n
instance : OfNat Address n where ofNat := Address.ofNat n
instance : OfNat Value n where ofNat := Value.ofNat n
instance : Coe RequestId Nat where coe := RequestId.toNat

instance : BEq ThreadId := @instBEq ThreadId instThreadIdDecidableEq
instance : Lean.Quote ThreadId where quote := λ n => Lean.quote (ThreadId.toNat n)
instance : ToString ConditionalValue where toString
  | .const n => s!"{n}"
  | .addOne => s!"n + 1"
  | .failed => "FAILED"

instance : LawfulBEq ThreadId := inferInstance
instance : LawfulBEq (List ThreadId) := inferInstance

def Address.prettyPrint (addr : Address) : String :=
  match (OfNat.ofNat addr) with
    | 0 => s!"x"
    | 1 => s!"y"
    | 2 => s!"z"
    | addr => s!"v{addr}"


inductive BlockingKinds
  | Read2ReadPred
  | Read2ReadNoPred
  | Read2WritePred
  | Read2WriteNoPred
  | Write2Read
  | Write2Write
  deriving BEq

abbrev BlockingSemantics := List BlockingKinds

def BlockingKinds.toString : BlockingKinds → String
  | .Read2ReadPred => "R → R (P)"
  | .Read2ReadNoPred => "R → R (NP)"
  | .Read2WritePred => "R → W (P)"
  | .Read2WriteNoPred => "R → W (NP)"
  | .Write2Read => "W → R"
  | .Write2Write => "W → W"

instance : ToString BlockingKinds where toString := BlockingKinds.toString

class ArchReq where
  (type : Type 0)
  (instBEq : BEq type)
  (instInhabited : Inhabited type)
  (instToString : ToString type)
  (prettyPrint : type → String := instToString.toString)
  (isPermanentRead : type → Bool := λ _ => false)

variable [ArchReq]

structure ReadRequest where
 addr : Address
 reads_from : Option RequestId
 atomic : Bool
 val : Value
 deriving BEq, Inhabited

structure WriteRequest where
 addr : Address
 val : ConditionalValue
 atomic : Bool
 deriving BEq, Inhabited

instance : BEq ArchReq.type := ArchReq.instBEq
instance : Inhabited ArchReq.type := ArchReq.instInhabited
instance : ToString ArchReq.type := ArchReq.instToString

inductive BasicRequest
 | read : ReadRequest → ArchReq.type → BasicRequest
 | write : WriteRequest → ArchReq.type → BasicRequest
 | fence : ArchReq.type → BasicRequest
 deriving BEq

instance : Inhabited BasicRequest where default := BasicRequest.fence default

def BasicRequest.toString : BasicRequest → String
  | BasicRequest.read  rr ty =>
    let tyStr := match s!"{ty}" with | "" => "" | str => s!". {str}"
    let atomicStr := if rr.atomic then "a" else ""
    s!"R{atomicStr}{tyStr} {rr.addr.prettyPrint}" ++ match rr.val with | none => "" | some v => s!" // {v}"
  | BasicRequest.write  wr ty =>
    let atomicStr := if wr.atomic then "a" else ""
    let tyStr := match s!"{ty}" with | "" => "" | str => s!". {str}"
    s!"W{atomicStr}{tyStr} {wr.addr.prettyPrint} {wr.val}"
  | BasicRequest.fence ty =>
    let tyStr := match s!"{ty}" with | "" => "" | str => s!". {str}"
    s!"Fence{tyStr}"

def BasicRequest.prettyPrint : BasicRequest → String
  | BasicRequest.read rr ty =>
    let valStr := match rr.val with
      | none => ""
      | some val => s!"({val})"
    let atomicStr := if rr.atomic then "a" else ""
    let tyStr := match s!"{ArchReq.prettyPrint ty}" with
      | "" => ""
      | str => s!".{str}"
    s!"R{atomicStr}{tyStr} {rr.addr.prettyPrint}{valStr}"
  | BasicRequest.write  wr ty =>
    let atomicStr := if wr.atomic then "a" else ""
    let tyStr := match s!"{ArchReq.prettyPrint ty}" with
      | "" => ""
      | str => s!".{str}"
    s!"W{atomicStr}{tyStr} {wr.addr.prettyPrint}({wr.val})"
  | BasicRequest.fence ty =>
    let tyStr := match s!"{ArchReq.prettyPrint ty}" with
      | "" => ""
      | str => s!".{str}"
    s!"Fence{tyStr}"

instance : ToString (BasicRequest) where toString := BasicRequest.toString

def BasicRequest.type : BasicRequest → ArchReq.type
  | BasicRequest.read  _ t => t
  | BasicRequest.write  _ t => t
  | BasicRequest.fence t => t

def BasicRequest.readRequest? : BasicRequest → Option ReadRequest
  | BasicRequest.read  rr _ => some rr
  | BasicRequest.write  _ _ => none
  | BasicRequest.fence _ => none

def BasicRequest.writeRequest? : BasicRequest → Option WriteRequest
  | BasicRequest.read  _ _ => none
  | BasicRequest.write  wr _ => some wr
  | BasicRequest.fence _ => none

def BasicRequest.updateType : BasicRequest → (ArchReq.type → ArchReq.type) → BasicRequest
  | .read  rr t, f => .read rr (f t)
  | .write  wr t, f => .write wr (f t)
  | .fence t, f => .fence (f t)

def BasicRequest.setValue : (BasicRequest) → Value → (BasicRequest)
  | BasicRequest.read rr rt, v => BasicRequest.read {rr with val := v} rt
  | br@_ , _ => br

def BasicRequest.updateValue : (BasicRequest) → Value → (BasicRequest)
  | BasicRequest.write wr rt, v => BasicRequest.write {wr with val := updateConditionalValue wr.val v} rt
  | br@_ , _ => br

def BasicRequest.value? : BasicRequest → Value
  | BasicRequest.read rr _ => rr.val
  | BasicRequest.write wr _ => match wr.val with
    | .const n => some n
    | .addOne => none
    | .failed => none
  | _ => none

structure ValidScopes where
  system_scope : List ThreadId
  scopes : ListTree ThreadId
  --scopes_consistent : ∀ s, scopes.elem s → s.sublist system_scope
  --system_scope_is_scope : system_scope ∈ scopes

def ValidScopes.default : ValidScopes :=
    { system_scope := [], scopes := ListTree.leaf [],
     -- scopes_consistent :=
     --     (by
     --      intros s h
     --      simp [ListTree.elem] at h
     --      rw [h]
     --      simp),
     -- system_scope_is_scope :=
     --     (by simp [ (· ∈ ·) ])
    }

instance : Inhabited ValidScopes where default := ValidScopes.default

def ValidScopes.toStringHet (threadType : Option (ThreadId → String)) (scopes : ValidScopes) : String :=
  let scopeFun := match threadType with
    | none => λ _ => ""
    | some f => λ ss =>
       let labs := removeDuplicates $ List.map f ss
       if labs == ["default"] || labs == [] then "" else
       if labs.length == 1 then labs.head! else
       String.intercalate "+" labs
  let scopeLab := λ s : List ThreadId => if s.isEmpty then "" else toString s ++ scopeFun s
  "{" ++ String.intercalate ", " (scopes.scopes.toList.map scopeLab) ++ "}"

def ValidScopes.toString (scopes : ValidScopes) : String := scopes.toStringHet none
instance : ToString ValidScopes where toString := ValidScopes.toString

open Lean in
private def quoteValidScopes : ValidScopes → Term
  | ValidScopes.mk system_scope scopes /-consistent system_is_scope-/ => Syntax.mkCApp ``ValidScopes.mk #[quote system_scope, quote scopes] -- , sorry, sorry]
instance : Lean.Quote ValidScopes where quote := quoteValidScopes

structure Scope {V : ValidScopes} where
  threads : List ThreadId
  valid : threads ∈ V.scopes

instance {V : ValidScopes} : ToString (@Scope V) where toString := λ ⟨threads,_⟩ => s!"{threads}"

instance {V : ValidScopes} : BEq (@Scope V) where
  beq := λ scope₁ scope₂ => scope₁.threads == scope₂.threads

instance {V : ValidScopes} : BEq (@Scope V) where
  beq := λ scope₁ scope₂ => scope₁.threads == scope₂.threads

instance {V : ValidScopes} : LE (@Scope V) where
  le := λ scope₁ scope₂ => List.sublist scope₁.threads scope₂.threads

structure Request where
  id : RequestId
  propagated_to : List ThreadId
  predecessor_at : List ThreadId
  thread : ThreadId
  basic_type : BasicRequest
  occurrence : Nat
  -- scope : Scope
  -- type : α
  deriving BEq


def Request.default : Request :=
  {id := 0, propagated_to := [], predecessor_at := [], thread := 0,
   occurrence := 0, basic_type := BasicRequest.fence Inhabited.default}
instance : Inhabited (Request) where default := Request.default

def Request.toString : Request → String
  | req => s!" Request {req.id} {req.basic_type.prettyPrint} : [propagated to {req.propagated_to}, origin thread : {req.thread}, pred. at : {req.predecessor_at}]"
instance : ToString (Request) where toString := Request.toString

def Request.toShortString : Request → String
  | req => s!"{req.id}[{req.basic_type.toString}]"

def BasicRequest.isRead    (r : BasicRequest) : Bool := match r with | read  _ _ => true | _ => false
def BasicRequest.isWrite   (r : BasicRequest) : Bool := match r with | write _ _ => true | _ => false
def BasicRequest.isFence (r : BasicRequest) : Bool := match r with | fence _ => true | _ => false

def BasicRequest.isAtomic (r : BasicRequest) : Bool := match r with | .read rr _ => rr.atomic | .write wr _ => wr.atomic | .fence _ => false
def Request.isRead    (r : Request) : Bool := r.basic_type.isRead
def Request.isWrite   (r : Request) : Bool := r.basic_type.isWrite
def Request.isFence (r : Request) : Bool := r.basic_type.isFence
def Request.isMem     (r : Request) : Bool := !r.basic_type.isFence
def Request.isPermanentRead (r : Request) : Bool := r.isRead && ArchReq.isPermanentRead r.basic_type.type

def Request.value? (r : Request) : Value := r.basic_type.value?
def Request.setValue (r : Request) (v : Value) : Request := { r with basic_type := r.basic_type.setValue v}
def Request.updateValue (r : Request) (v : Value) : Request :=
  { r with basic_type := r.basic_type.updateValue v}
def Request.isSatisfied (r : Request) : Bool := match r.basic_type with
  | .read rr _ => rr.val.isSome
  | _ => false

def Request.isAtomic (r : Request) : Bool := r.basic_type.isAtomic

def BasicRequest.address? (r : BasicRequest) : Option Address := match r with
  | read  req _ => some req.addr
  | write req _ => some req.addr
  | _ => none

def Request.address? (r : Request) : Option Address := r.basic_type.address?

def Request.equivalent (r₁ r₂ : Request) : Bool :=
  if r₁.isFence then r₁.basic_type == r₂.basic_type
  else r₁.address? == r₂.address? && r₁.value? == r₂.value? && r₁.thread == r₂.thread

-- Read, Write
def SatisfiedRead := RequestId × RequestId deriving ToString, BEq

--instance [BEq α] : Membership (List α) (ListTree α) where
--  mem lst tree := tree.elem lst = true

def decideThreadsValid (threads : List ThreadId) (V : ValidScopes) : Decidable (threads ∈ V.scopes) :=
  if h : V.scopes.elem threads then
    Decidable.isTrue h
  else
    Decidable.isFalse h

instance {threads : List ThreadId} {V : ValidScopes} : Decidable (threads ∈ V.scopes) := decideThreadsValid threads V

def ValidScopes.validate (V : ValidScopes) (threads : List ThreadId) : Option (@Scope V) :=
    if h : threads ∈ V.scopes then
        some { threads := threads, valid := h }
    else
        none

-- Gives the subscopes of S, including S.
def ValidScopes.subscopes (V : ValidScopes) (S : @Scope V) : List (@Scope V) :=
  let children := V.scopes.nodesBelow S.threads
  filterNones $ children.map V.validate

def ValidScopes.containThread (V: ValidScopes) (t : ThreadId) : List (@Scope V) :=
  let containing := V.scopes.nodesAbove [t]
  filterNones $ containing.map V.validate

def ValidScopes.systemScope {V : ValidScopes } : @Scope V :=
  {threads := V.system_scope, valid := sorry} -- V.system_scope_is_scope}

instance {V : ValidScopes} : Inhabited (@Scope V) where
 default := V.systemScope

def ValidScopes.isUnscoped (V : ValidScopes) : Bool :=
  V.scopes == (ListTree.leaf V.system_scope)

def ValidScopes.jointScope : (V : ValidScopes) → ThreadId → ThreadId → (@Scope V)
 | valid, t₁, t₂ => match valid.scopes.meet t₁ t₂ with
   | some scope => {threads := scope, valid := sorry}
   | none => panic! s!"can't find the joint scope of {t₁} and {t₂} in {valid.scopes}"-- can we get rid of this case distinction?

def ValidScopes.reqThreadScope (V : ValidScopes ) (req : Request) : (@Scope V) :=
   V.jointScope req.thread req.thread

def ValidScopes.intersection : (V : ValidScopes) → @Scope V → @Scope V → Option (@Scope V)
  | V, s1, s2 => V.validate $ s1.threads.intersection s2.threads

def Request.propagatedTo (r : Request) (t : ThreadId) : Bool := r.propagated_to.elem t

def Request.fullyPropagated {V : ValidScopes}  (r : Request) (s : optParam (@Scope V) V.systemScope) : Bool :=
  let propToList := s.threads.map (λ t => Request.propagatedTo r t)
  propToList.foldl (init:= true) (. && .)

def Request.isPredecessorAt (req : Request) (thId : ThreadId) : Bool :=
  req.predecessor_at.contains thId

def Request.makePredecessorAt (req : Request) (thId : ThreadId) : Request :=
  if req.isPredecessorAt thId then req else { req with predecessor_at := thId :: req.predecessor_at}

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

-- TODO: make scope an optional parameter and just do the intersection by default?
-- Would need to move around things in Arch typeclass...
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

 def OrderConstraints.transitiveSuccessors {V : ValidScopes} (S : @Scope V) (req : RequestId)
   (reqs : List RequestId) (constraints : @OrderConstraints V)  : List RequestId :=
   let sc_oc := constraints.lookup S
   Id.run do
     let mut succ := []
     let mut succ' := [req]
     while succ != succ' do
       succ := succ'
       succ' := reqs.filter
         λ x => succ'.any
           λ s => x == s || sc_oc s x
     return succ'

def OrderConstraints.between {V : ValidScopes} (S : @Scope V) (req₁ req₂ : RequestId)
  (reqs : List RequestId) (constraints : @OrderConstraints V)  : List RequestId :=
  let preds₁ := constraints.predecessors S req₁ reqs
  let preds₂ := constraints.predecessors S req₂ reqs
  preds₂.removeAll (req₁::preds₁)

-- TODO: is this really a quasi top sort?
def OrderConstraints.qtopSort {V : ValidScopes} (S : @Scope V)
  (reqs : List Request) (constraints : @OrderConstraints V)  : List Request :=
  reqs.toArray.qsort (λ r₁ r₂ => constraints.lookup S r₁.id r₂.id) |>.toList

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
      keys.all λ (s,r₁,r₂) => match s with
        | (some s₁, some s₂) => (oc₁.lookup s₁ r₁ r₂ == oc₂.lookup s₂ r₁ r₂)
        | _ => panic! s!"invalid scopes {scopes₁} or {scopes₂}"

def OrderConstraints.addSingleScope {V : ValidScopes} (constraints : @OrderConstraints V)
  (scope : @Scope V) (reqs : List (RequestId × RequestId)) (val := true) : @OrderConstraints V :=
  match constraints.val.find? scope.threads with
   | none => constraints
   | some sc_oc =>
       let sc_oc' := reqs.foldl (init := sc_oc) λ oc req => oc.insert req val
       let val' := constraints.val.insert scope.threads sc_oc'
       { constraints with val := val' }

-- Updates `constraints` to add all pairs in `reqs` to the scope `scope` and each
-- of its suscopes. The optional value `val` is what the constraint is updated to,
-- and defaults to `true`.
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

def OrderConstraints.groupsToString : List Request → List Request → String
  | [],_ => ""
  | _,[] => ""
  | reqs₁, reqs₂ =>
    let vars₁ := removeDuplicates $ reqs₁  |>.map Request.address?
    let vars₂ := removeDuplicates $ reqs₂  |>.map Request.address?
    let vars := vars₁.filter vars₂.contains
    let colorFun := λ r => if vars.contains r.address? && r.address?.isSome then
      colorString Color.magenta r.toShortString else r.toShortString
    let (r₁strings, r₂strings) := (reqs₁.map colorFun, reqs₂.map colorFun)
    "{" ++ (String.intercalate ", " $ r₁strings) ++
                    "} → {" ++ (String.intercalate ", " $ r₂strings) ++ "}"

def OrderConstraints.toString {V : ValidScopes} (constraints : @OrderConstraints V) (scope : @Scope V) (reqs : List Request) : String := Id.run do
   let reqsSorted := constraints.qtopSort scope reqs
   let mut pairs := []
   for req in reqsSorted do
     let deps := reqsSorted.filter λ req' => constraints.lookup scope req.id req'.id
       if deps.isEmpty then
         continue
       pairs := pairs ++ [ (req,deps) ]
   let mut res : List (List Request × List Request) := []
   for (req,deps) in pairs do
     if res.any λ (lhs,_) => lhs.contains req then
       continue
     let mut lhs := [req]
     for req' in reqsSorted do
       if req' == req then
         continue
       if pairs.lookup req' == some deps then
         lhs := req'::lhs
     res := res ++ [(lhs,deps)]
   String.intercalate ";   " $ res.map λ (lhs,rhs) => OrderConstraints.groupsToString lhs rhs

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

def RequestArray.getReq? : RequestArray → RequestId → Option (Request)
  | arr, rId => match arr.val[rId.toNat]? with
    | some (some req) => some req
    | _ => none

def RequestArray.getReq! : RequestArray → RequestId → Request
  | arr, rId => arr.val[rId.toNat]?.get!.get!

def RequestArray.printReq : RequestArray → RequestId → String
  | arr, rId => match arr.getReq? rId with
    | none => ""
    | some r => r.toShortString

def RequestArray.seen : RequestArray → List RequestId
  | arr => List.range arr.val.size

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

def RequestArray.prettyPrint (arr : RequestArray) (numThreads : Nat) (order : @OrderConstraints V) (colWidth := 25) (highlight : optParam (Option $ ThreadId × RequestId) none) : String := Id.run do
  let mut threads := []
  let mut res := ""
  for thId in (List.range numThreads) do
    if thId != 0 then
      res := res ++ "||"
    res := res ++ s!" T{thId}" ++ (String.mk $ List.replicate (colWidth - 3) ' ')
    let mut thread := []
    for req in arr.filter (λ r => !(r.isWrite && r.value? == some 0)) do
      if highlight == some (thId, req.id) then
        thread := thread ++ [(Color.yellow, req)]
      else if req.thread == thId then
        thread := thread ++ [(Color.cyan, req)]
      else if req.propagatedTo thId then
        thread := thread ++ [(Color.black, req)]
    threads := threads ++ [thread]
  res := res ++ "|\n" ++ (String.mk $ List.replicate (colWidth * numThreads + 2 * (numThreads - 1)) '-') ++ "\n"
  threads := threads.map
    (λ th => th.toArray.qsort
      (λ r₁ r₂ => order.lookup (V.jointScope r₁.2.thread r₂.2.thread) r₁.2.id r₂.2.id)
        |>.toList)
  while threads.any (!·.isEmpty) do
    let mut sep := false
    for thread in threads do
      if sep then
        res := res ++ "||"
      else
        sep := true
      res := res ++ match thread.head? with
        | none => (String.mk $ List.replicate colWidth ' ')
        | some (color,r) => " " ++ (colorString color r.toShortString) ++ (String.mk $ List.replicate (colWidth - r.toShortString.length - 1) ' ')
    res := res ++ "|\n"
    threads := threads.map List.tail
  return res

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
    -- If we use `i.toNat == vals'.size` then Lean won't unfold the typeclass
    -- instance of BEq.beq (which is Nat.beq) and we can't use Nat.beq_eq.
    -- Maybe ask on Zulip?
    else if h: (Nat.beq i.toNat vals'.size) then
      let hless : i.toNat < vals'.size + 1 := by
        {apply Nat.lt_of_succ_le
         apply Nat.le_of_eq
         rw [Nat.succ_eq_add_one]
         rw [Nat.beq_eq] at h
         rw [h]
         }
      let idfin := Fin.mk i.toNat hless
      vals'.insertAt idfin (some req)
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

-- Inserst request at the position given by its id.
-- Will overwrite another request with that same id.
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
  removed : List (Request) -- TODO: remove, def. "active" to ignore satisfied reads
  scopes : ValidScopes
  satisfied : List SatisfiedRead
  threadTypes : ThreadId → String
  orderConstraints : @OrderConstraints scopes
  removedCoherent : ∀ id : RequestId, id ∈ (removed.map Request.id) → id ∈ reqIds requests

def SystemState.beq (state₁ state₂ : SystemState)
  -- (samesystem : state₁.system = state₂.system)
  : Bool :=
  state₁.requests == state₂.requests &&
  state₁.removed == state₂.removed &&
  state₁.satisfied == state₂.satisfied &&
  -- this will be expensive!
  state₁.orderConstraints.compare state₂.orderConstraints (reqIds state₁.requests)

instance : BEq (SystemState) where beq := SystemState.beq

def SystemState.findMaybeRemoved? (state : SystemState) (rId : RequestId) : Option Request :=
  match state.requests.getReq? rId with
    | some r => some r
    | none => state.removed.find? (·.id == rId)

def SystemState.oderConstraintsString (state : SystemState)
(scope : optParam (@Scope state.scopes) state.scopes.systemScope) : String :=
  state.orderConstraints.toString scope $ filterNones $ state.requests.val.toList

def SystemState.threads : SystemState → List ThreadId
 | s => s.scopes.system_scope

def SystemState.prettyPrint (state : SystemState) (highlight : optParam (Option $ ThreadId × RequestId) none) : String :=
  let ocString := if state.scopes.scopes.toList.length == 1
    then s!"constraints: {state.oderConstraintsString}\n"
    else String.intercalate "\n" $ state.scopes.scopes.toList.map
      λ scope => s!"constraints (scope {scope}) : {state.oderConstraintsString (state.scopes.validate scope).get!}"
  let satisfiedStr := state.satisfied.map
    λ (r₁, r₂) => s!"{(state.findMaybeRemoved? r₁).get!.toShortString} with {state.requests.printReq r₂}"
  s!"requests:\n{state.requests.toString}\n\n"++
  s!"{state.requests.prettyPrint state.threads.length state.orderConstraints (highlight := highlight)}\n"  ++
  s!"removed: {state.removed.toString}\n" ++
  s!"satisfied: {satisfiedStr}\n" ++
  ocString

def SystemState.toString : SystemState → String
  | state =>
  let ocString := if state.scopes.scopes.toList.length == 1
    then s!"constraints: {state.oderConstraintsString}\n"
    else String.intercalate "\n" $ state.scopes.scopes.toList.map
      λ scope => s!"constraints (scope {scope}) : {state.oderConstraintsString (state.scopes.validate scope).get!}"
  let satisfiedStr := state.satisfied.map
    λ (r₁, r₂) => s!"{(state.findMaybeRemoved? r₁).get!.toShortString} with {state.requests.printReq r₂}"
  s!"requests:\n{state.requests}\n"  ++
  s!"removed: {state.removed.toString}\n" ++
  s!"satisfied: {satisfiedStr}\n" ++
  ocString

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

def SystemState.init (S : ValidScopes) (threadTypes : ThreadId → String): SystemState :=
  { requests := RequestArray.empty, removed := [],
    scopes := S, satisfied := [], orderConstraints := OrderConstraints.empty,
    removedCoherent := emptyCoherent RequestArray.empty, threadTypes
  }

def SystemState.default := SystemState.init ValidScopes.default (λ _ => "default")
instance : Inhabited (SystemState) where default := SystemState.default

def SystemState.seen : SystemState → List RequestId
  | state => state.requests.seen

def SystemState.idsToReqs : SystemState → List RequestId → List (Request)
  | state, ids => filterNones $ ids.map (λ id => state.requests.getReq? id)

def SystemState.isSatisfied : SystemState → RequestId → Bool
  | state, rid =>
  !(state.satisfied.filter λ (srd,_) => srd == rid).isEmpty

def SystemState.reqPropagatedTo : SystemState → RequestId → ThreadId → Bool
  | state, rid, tid => match state.requests.getReq? rid with
    | none => false
    | some req => req.propagatedTo tid

def SystemState.updateRequest : SystemState → Request → SystemState
  | state, request =>
   let requests' := state.requests.insert request
   SystemState.mk requests' state.removed state.scopes state.satisfied
   state.threadTypes state.orderConstraints sorry
   --{requests := requests', seen := state.seen, removed := state.removed,
   -- scopes := state.scopes, satisfied := state.satisfied,
   -- orderConstraints := state.orderConstraints,
   -- seenCoherent := state.seenCoherent, removedCoherent := state.removedCoherent,
   -- satisfiedCoherent := state.satisfiedCoherent}
def SystemState.allRequests (state : SystemState) : List Request := state.removed ++ filterNones state.requests.val.toList

class Arch where
  (req : ArchReq)
  (orderCondition : ValidScopes → Request → Request → Bool)
  (blockingSemantics : Request → BlockingSemantics)
  (scopeIntersection : (valid : ValidScopes) → Request → Request → @Scope valid := λ v _ _ => v.systemScope)
  (predecessorConstraints : SystemState → RequestId → RequestId → Bool := λ _ _ _ => true)
  (acceptConstraints : SystemState → BasicRequest → ThreadId → Bool := λ _ _ _ => true)
  (acceptEffects : SystemState → RequestId → ThreadId → SystemState := λ st _ _ => st)
  (propagateConstraints : SystemState → RequestId → ThreadId → Bool := λ _ _ _ => true)
  (propagateEffects : SystemState → RequestId → ThreadId → SystemState := λ st _ _ => st)
  (satisfyReadConstraints : SystemState → RequestId → RequestId → Bool := λ _ _ _ => true)
  (satisfyReadEffects : SystemState → RequestId → RequestId → SystemState := λ st _ _ => st)

def Request.blockingSemantics  [inst : Arch] (req : @Request inst.req) : BlockingSemantics := Arch.blockingSemantics req

end Pop
