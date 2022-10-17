import Pop.States
import Pop.Litmus
import Pop.Util

open Pop Util

namespace PTX

inductive Scope
  | cta
  | gpu
  | sys
  deriving Inhabited, BEq, Repr

inductive Semantics
  | sc
  | acqrel
  | rel
  | acq
  | rlx
  | weak
  deriving Inhabited, BEq, Repr

structure Req where
  (scope : Scope)
  (sem : Semantics)
  (predecessorAt : List ThreadId)
  deriving BEq

def Req.isStrong (req : Req) : Bool :=
  match req.sem with
  | .weak => false
  | _ => true

instance : Inhabited Req where default :=
  { scope := Scope.sys, sem := Semantics.sc, predecessorAt := []}

def Scope.toString : Scope → String
  | .cta => "cta"
  | .gpu => "gpu"
  | .sys => "sys"

def Semantics.toString : Semantics → String
  | .sc => "sc"
  | .acqrel => "acqrel"
  | .rel => "rel"
  | .acq => "acq"
  | .rlx => "rlx"
  | .weak => "weak"

instance : ToString Scope where toString := Scope.toString
instance : ToString Semantics where toString := Semantics.toString

def Req.toString (req : Req) : String :=
  match req.sem, req.scope with
  | .rlx, .sys => ""
  | sem, scope => s!"{scope}_{sem}"

def Req.prettyPrint (req : Req) : String :=
  let predStr :=
    match req.predecessorAt with
      | [] => ""
      | preds => s!" pred @ {preds}"
  req.toString ++ predStr

instance : ToString Req where toString := Req.toString

instance : ArchReq where
  type := PTX.Req
  instBEq := PTX.instBEqReq
  instInhabited := PTX.instInhabitedReq
  isPermanentRead := λ _ => false
  instToString := PTX.instToStringReq
  prettyPrint := Req.prettyPrint

def getThreadScope (valid : ValidScopes) (thread : ThreadId) (scope : Scope) :=
  let containing := valid.containThread thread
  -- TODO: Could I get rid of this sorting (from the ListTree structure)?
    |>.toArray |>.qsort (λ l₁ l₂ => l₁.threads.length < l₂.threads.length)
  match scope with
  | .sys => valid.systemScope
  | .cta => if let some cta := containing[0]?
    then cta
    else panic! "invalid cta scope"
  | .gpu =>
  if let some cta := containing[0]?
    then
      let remaining := containing.erase cta
      if let some gpu := remaining[0]?
      then gpu
      else panic! "invalid gpu scope (not enough scopes)"
    else panic! "invalid gpu scope"

def requestScope (valid : ValidScopes) (req : Request) : @Pop.Scope valid :=
  getThreadScope valid req.thread req.basic_type.type.scope

def scopeInclusive (V : ValidScopes) (r₁ r₂ : Request) : Bool :=
  let (t₁,t₂) := (r₁.thread, r₂.thread)
  let scope₁ := requestScope V r₁
  let scope₂ := requestScope V r₂
  scope₁.threads.contains t₂ && scope₂.threads.contains t₁

def morallyStrong (V : ValidScopes) (r₁ r₂ : Request) : Bool :=
  r₁.basic_type.type.isStrong && r₂.basic_type.type.isStrong && scopeInclusive V r₁ r₂

end PTX

namespace Pop
def Request.sem (req : Request) : PTX.Semantics :=
  req.basic_type.type.sem

-- some shortcuts
def Request.isFenceSC (req : Request) : Bool :=
  req.isFence && req.basic_type.type.sem == PTX.Semantics.sc

def Request.isFenceAcqRel (req : Request) : Bool :=
  req.isFence && req.basic_type.type.sem == PTX.Semantics.acqrel

def Request.isRel (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.rel

def Request.isGeqRel (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.rel ||
  req.basic_type.type.sem == PTX.Semantics.acqrel ||
  req.basic_type.type.sem == PTX.Semantics.sc

def Request.isAcq (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.acq

def Request.isGeqAcq (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.acq ||
  req.basic_type.type.sem == PTX.Semantics.acqrel ||
  req.basic_type.type.sem == PTX.Semantics.sc

def Request.isAcqRelKind (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.rel ||
  req.basic_type.type.sem == PTX.Semantics.acq ||
  req.basic_type.type.sem == PTX.Semantics.acqrel ||
  req.basic_type.type.sem == PTX.Semantics.sc

def Request.predecessorAt (req : Request) : List ThreadId :=
  req.basic_type.type.predecessorAt

def Request.makePredecessorAt (req : Request) (thId : ThreadId) : Request :=
  let predList := req.basic_type.type.predecessorAt
  --dbg_trace "Making {req} a predecessor at T{thId}"
  if predList.contains thId then
    req
  else
    let updateFun := λ t => { t with predecessorAt := thId::predList : PTX.Req}
    { req with basic_type := req.basic_type.updateType updateFun}

end Pop

namespace PTX

/-
  SC fence only considers its scope for order constraints.
  Scopes for rel, acq, acqrel (i.e. non-SC) fences:
    | W → Fence | Fence |
    | Fence → W |   ∩   |
    | R → Fence |   ∩   |
    | Fence → R | Fence |
    TODO: also do this for rel/acq reads/writes
-/
def scopesMatch : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
  -- For SC Fences we only consider their scope, and not the other request's
  if r_old.isFenceSC then
    (requestScope V r_old).threads.contains r_new.thread
  else if r_new.isFenceSC then
    (requestScope V r_new).threads.contains r_old.thread
  -- by above, not SC ⇒ rel, acq or acqrel
  else if r_old.isWrite && r_new.isAcqRelKind then
    (requestScope V r_new).threads.contains r_old.thread
  else if r_new.isAcqRelKind && r_new.isRead then
    (requestScope V r_old).threads.contains r_new.thread
  -- If neither is an SC fence, then we consider their joint scope
  else scopeInclusive V r_old r_new

def order : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
  -- TODO: we are not sure if this might make our model stronger than necessary
  let fences := (r_old.isFence && r_new.isFence)
                       && (r_old.thread == r_new.thread)
  /-
  r -> / Acq -> r/w; r/w -> acqrel r/w except (w -> r); r/w -> rel -> w
  -/
  let acqafter := r_old.isGeqAcq && (r_new.thread == r_old.thread)
  let acqread :=  r_new.isGeqAcq && (r_new.thread == r_old.thread && r_old.isRead)
   -- TODO: why also for diff. threads? should this be handled with predeecessors?
  let newrel := r_new.isGeqRel
  let relwrite := r_old.isGeqRel && (r_new.thread == r_old.thread || !r_new.isWrite)
  -- TODO: what about acqrel and (w -> r)?
  -- dbg_trace "[reorder] {r_old} {r_new}"
  -- dbg_trace "[reorder] fences : {fences}"
  -- dbg_trace "[reorder] satisfied : {satisfied}"
  -- dbg_trace "[reorder] relacq : {relacq}"
  -- dbg_trace "[reorder] relafter : {relbefore}"
  -- dbg_trace "[reorder] acqbefore : {acqafter}"
  -- dbg_trace "[reorder] newrel : {newrel}"
  -- dbg_trace "[reorder] !scopes match: {!scopesMatch V r_old r_new}"
  scopesMatch V r_old r_new &&
  (acqafter || newrel || fences || acqread || relwrite)

-- On SC fence we propagate predecessors to the SC fence's scope. We enforce
-- this by not accepting, propagating or satisfying any other requests unless
-- this is propagated. This is the check we use for that. Returns the first
-- SC fence that it finds that it's blocked on (it should never be more than
-- one anyway)
private def _root_.Pop.SystemState.blockedOnFencePreds (state : SystemState) (fence : Request) : List Request := Id.run do
  let mut res := []
  let scope := PTX.requestScope state.scopes fence
  if fence.fullyPropagated scope then
    return res
  else
    let preds := state.requests.filter
      λ r => r.predecessorAt.contains fence.thread ||
             -- TODO: why this second constraint?
             r.propagatedTo fence.thread && r.id != fence.id
    res := res ++ preds
  return res

def reqRFEstablishedScope (state : SystemState) (scope : @Pop.Scope state.scopes) (r : Request) : Bool :=
    let precidingWrites := filterNones $ state.orderConstraints.predecessors scope r.id state.seen |>.map
        λ predId => match state.requests.getReq? predId with
          | none => none
          | some req => if req.isWrite then
              some req else
              none
    state.isSatisfied r.id || (r :: precidingWrites).all (·.fullyPropagated scope)


def _root_.Pop.SystemState.blockedOnRequests (state : SystemState) : List RequestId := Id.run do
  let fences := state.requests.filter Request.isAcqRelKind
  let mut res := []
  for fence in fences do
    let preds := state.blockedOnFencePreds fence
    let scope := PTX.requestScope state.scopes fence
    -- This is the change, blocking when unsatisfied reads (breaks MP_fence_cta_1fence)
    let readsOnThread := state.requests.filter λ r => r.isRead &&  r.thread == fence.thread
    unless readsOnThread.all (reqRFEstablishedScope state scope) do
      --dbg_trace "blocked on Fence (R{fence.id}) with unsatisfied reads ({readsOnThread.map λ r => (r,reqRFEstablishedScope state scope r)}) "
      res := res ++ [fence.id]
      continue
    unless !fence.isFenceSC || preds.all λ p => p.fullyPropagated scope do
      --dbg_trace "blocked on FenceSC (R{fence.id}) with unpropagated predecessors ({preds}) to scope {scope}"
       res := res ++ [fence.id]
  return res


def acceptConstraintsAux (state : SystemState) (br : BasicRequest) (tid : ThreadId) (reqs : List RequestId) : Bool :=
    match reqs with
      | [] =>
        let scfences := state.requests.filter Request.isFenceSC
        scfences.all λ r =>  r.thread != tid || r.fullyPropagated (requestScope state.scopes r)
      | reqId::rest =>
        let req := state.requests.getReq! reqId
        if req.isFenceSC then
          false
        else if req.thread != tid then
          acceptConstraintsAux state br tid rest
        else
          let readsOnThread := state.requests.filter λ r => r.isRead &&  r.thread == tid
          let scope := requestScope state.scopes req
          readsOnThread.all (reqRFEstablishedScope state scope) && acceptConstraintsAux state br tid rest
            --(r.fullyPropagated scope && (precedingWrites state r scope).all λ pred => pred.fullyPropagated scope)

def acceptConstraints (state : SystemState) (br : BasicRequest) (tid : ThreadId) : Bool :=
    acceptConstraintsAux state br tid state.blockedOnRequests

def propagateConstraints (state : SystemState) (rid : RequestId) (thId : ThreadId) : Bool :=
  state.blockedOnRequests.all
    λ fenceId =>
      let fence := state.requests.getReq! fenceId
      let scope := PTX.requestScope state.scopes fence
      if fence.isFenceSC && scope.threads.contains thId then
        let preds := state.blockedOnFencePreds fence |>.map Request.id
        let req := state.requests.getReq! rid
        preds.contains rid || (req.isRead && req.thread == fence.thread)
      else true

-- on a (rel/acq/acqrel) fence we add an edge from each pred to this fence
-- according to the scopes-match table
def addEdgesOnFence (state : SystemState) : SystemState := Id.run do
  let fences := state.requests.filter λ r => r.isFence &&
    !(r.fullyPropagated (requestScope state.scopes r))
  let mut st := state
  for fence in fences do
    let scope := requestScope st.scopes fence
    let preds := state.requests.filter λ r => r.predecessorAt.contains fence.thread
    let newConstraintPairs := preds.map Request.id |>.zip (List.replicate preds.length fence.id)
    let oc' := st.orderConstraints.addSubscopes scope newConstraintPairs
    st := { st with orderConstraints := oc' }
   return st

def propagateEffects (state : SystemState) (reqId : RequestId) (thId : ThreadId)
: SystemState := Id.run do
  -- add predecessors as soon as RF edge formed
  let req := state.requests.getReq! reqId
  if !req.isWrite then
     return state
  else
    let mut res := state
    let successors := state.orderConstraints.successors (state.scopes.jointScope req.thread thId) reqId state.seen
    for reqId' in successors do
      if let some req' := state.requests.getReq? reqId' then
        if req'.isRead && morallyStrong state.scopes req req' then
          res := res.updateRequest $ req.makePredecessorAt thId
    return res
/-
 * A predecessor should behave *as if* it was in that same thread.
 * We add edge between predecessor and fence always (?):  maybe only for ≥release?
 * Add predecessor only at RF (not at propagate)
-/
def acceptEffects (state : SystemState) (reqId : RequestId) (thId : ThreadId) :=
  let propState := propagateEffects state reqId thId
  if (state.requests.getReq! reqId).isFence then addEdgesOnFence propState else propState

def satisfyReadEffects : SystemState → RequestId → RequestId → SystemState
  | state, _, _ => addEdgesOnFence state
  -- TODO: also add fence-pred edges here

instance : Arch where
  req := instArchReq
  acceptConstraints := acceptConstraints
  propagateConstraints := propagateConstraints
  orderCondition := order
  requestScope := requestScope
  acceptEffects := acceptEffects
  propagateEffects := propagateEffects
  satisfyReadEffects := satisfyReadEffects

namespace Litmus
def mkRead (scope_sem : String ) (addr : Address) (_ : String) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.read rr
              {scope := Scope.sys, sem := Semantics.rlx, predecessorAt := []}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          dbg_trace "(read) invalid PTX scope: {scopeStr}"
          Scope.sys
      let sem := match semStr with
        | "acq" => Semantics.acq
        | "rlx" => Semantics.rlx
        | "weak" => Semantics.weak
        | _ =>
          dbg_trace "(read) invalid PTX semantics: {semStr}"
          Semantics.weak
      BasicRequest.read rr
      {scope := scope, sem := sem, predecessorAt := []}
    | _ =>
      dbg_trace "malformed PTX read request: W.{scope_sem}"
      BasicRequest.read rr default

def mkWrite (scope_sem : String) (addr : Address) (val : Value) (_ : String) : BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := val}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.write wr
              {scope := Scope.sys, sem := Semantics.rlx, predecessorAt := []}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          dbg_trace "(write) invalid PTX scope: {scopeStr}"
          Scope.sys
      let sem := match semStr with
        | "rel" => Semantics.rel
        | "rlx" => Semantics.rlx
        | "weak" => Semantics.weak
        | _ =>
          dbg_trace "(write) invalid PTX semantics: {semStr}"
          Semantics.weak
      BasicRequest.write wr {scope := scope, sem := sem, predecessorAt := []}
    | _ =>
      dbg_trace "malformed PTX read request: W.{scope_sem}"
      BasicRequest.write wr default

def mkFence (scope_sem : String) (_ : String) : BasicRequest :=
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.fence
              {scope := Scope.sys, sem := Semantics.sc, predecessorAt := []}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          dbg_trace "(fence) invalid PTX scope: {scopeStr}"
          Scope.sys
      let sem := match semStr with
        | "sc" => Semantics.sc
        | "acqrel" => Semantics.acqrel
        | "rel" => Semantics.rel
        | "acq" => Semantics.acq
        | _ =>
          dbg_trace "(fence) invalid PTX semantics: {semStr}"
          Semantics.sc
      BasicRequest.fence {scope := scope, sem := sem, predecessorAt := []}
    | _ =>
      dbg_trace "malformed PTX read request: Fence.{scope_sem}"
      BasicRequest.fence default

def mkInitState (n : Nat) :=
  match n with
  | _ =>
  let valid_scopes : ValidScopes :=
    { system_scope := List.range n, scopes := ListTree.leaf (List.range n)}
  SystemState.init valid_scopes

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkFence := mkFence

end Litmus
