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

def Scope.intersection : Scope → Scope → Scope
  | .cta, _ => cta
  | .gpu, .cta => cta
  | .gpu, _ => .gpu
  | .sys, s => s

infixl:85 "∩" => Scope.intersection

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
  deriving BEq

def Req.isStrong (req : Req) : Bool :=
  match req.sem with
  | .weak => false
  | _ => true

instance : Inhabited Req where default :=
  { scope := Scope.sys, sem := Semantics.sc}

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

instance : ToString Req where toString := Req.toString

instance : ArchReq where
  type := PTX.Req
  instBEq := PTX.instBEqReq
  instInhabited := PTX.instInhabitedReq
  isPermanentRead := λ _ => false
  instToString := PTX.instToStringReq

def toAlloy : String → BasicRequest → String
    | moduleName, .read _ ty =>
      match ty.sem with
        | .acq => moduleName ++ "/Acquire"
        | _ => moduleName ++ "/Read - ptx/Acquire"
    | moduleName, .write _ ty =>
      match ty.sem with
        | .rel => moduleName ++ "/Release"
        | _ => moduleName ++ "/Write - ptx/Release"
    | moduleName, .fence ty =>
      match ty.sem with
        | .sc => moduleName ++ "/FenceSC"
        | .acqrel => moduleName ++ "/FenceAcqRel"
        | .rel => moduleName ++ "/FenceRel"
        | .acq => moduleName ++ "/FenceAcq"
        | _ => moduleName ++ "/Fence"
def alloyName := "ptx"

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

private def requestScope (valid : ValidScopes) (req : Request) : @Pop.Scope valid :=
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

def Request.markedScope (req : Request) : PTX.Scope :=
  req.basic_type.type.scope

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

def Request.isFenceLike (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.rel ||
  req.basic_type.type.sem == PTX.Semantics.acq ||
  req.basic_type.type.sem == PTX.Semantics.acqrel ||
  req.basic_type.type.sem == PTX.Semantics.sc

end Pop

namespace PTX

/-
  SC fence only considers its scope for order constraints.
  Scopes for rel, acq, acqrel (i.e. non-SC) fences:
    | W → Fence | Fence |
    | Fence → W |   ∩   |
    | R → Fence |   ∩   |
    | Fence → R | Fence |
-/
def scopeIntersection : (V : ValidScopes) → Request → Request → @Pop.Scope V
  | V, r_old, r_new => Id.run do
    let old_scope := PTX.requestScope V r_old
    let new_scope := PTX.requestScope V r_new
    let intersection := V.intersection old_scope new_scope
    if r_new.isGeqRel then
      return new_scope
    if r_old.isGeqAcq then
      return old_scope
    return intersection

def scopesMatch : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
    let scope := scopeIntersection V r_old r_new |>.threads
    scope.contains r_old.thread && scope.contains r_new.thread

def order : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
  -- TODO: we are not sure if this might make our model stronger than necessary
  let fences := (r_old.isFence || r_new.isFence)
                       && (r_old.thread == r_new.thread)
  /-
  r -> / Acq -> r/w; r/w -> acqrel r/w except (w -> r); r/w -> rel -> w
  -/
  let samemem_reads := r_old.address? == r_new.address? && r_old.isRead && r_new.isRead
  let acqafter := r_old.isGeqAcq && (r_new.thread == r_old.thread)
  let acqread :=  r_new.isGeqAcq && (r_new.thread == r_old.thread && r_old.isRead)
   -- TODO: why also for diff. threads? should this be handled with predeecessors?
  let newrel := r_new.isGeqRel && (r_new.thread == r_old.thread || r_old.isPredecessorAt r_new.thread)
  let relwrite := r_old.isGeqRel && r_new.thread == r_old.thread && r_new.isWrite
  let pred := r_old.isPredecessorAt r_new.thread && r_new.isFenceLike
  -- TODO: what about acqrel and (w -> r)?
   -- dbg_trace "[order] {r_old} {r_new}"
   -- dbg_trace "[order] fences : {fences}"
   -- dbg_trace "[order] acqafter : {acqafter}"
   -- dbg_trace "[order] acqread : {acqread}"
   -- dbg_trace "[order] newrel : {newrel}"
   -- dbg_trace "[order] relwrite : {relwrite}"
   -- dbg_trace "[order] scopes match: {scopesMatch V r_old r_new}"
  scopesMatch V r_old r_new &&
  (acqafter || newrel || fences || acqread || relwrite || pred || samemem_reads)

def allReadsDone (state : SystemState) (fenceLike : Request) : Bool :=
    let readsOnThread := state.requests.filter λ r => r.isRead &&  r.thread == fenceLike.thread &&
                          state.orderConstraints.lookup (state.scopes.reqThreadScope fenceLike) r.id fenceLike.id

    -- All fences block on reads (this implies acq does not block on preds)
    readsOnThread.all λ r =>
        let scope := scopeIntersection state.scopes r fenceLike
        state.isSatisfied r.id || r.fullyPropagated scope

def memPredsDone (state : SystemState) (fenceLike : Request) : Bool :=
    let preds := state.requests.filter λ r => r.isPredecessorAt fenceLike.thread
    let memopsOnThread := state.requests.filter λ r => r.isMem &&  r.thread == fenceLike.thread &&
                          state.orderConstraints.lookup (state.scopes.reqThreadScope fenceLike) r.id fenceLike.id
    let fenceScope := PTX.requestScope state.scopes fenceLike
    (memopsOnThread ++ preds).all λ w => w.fullyPropagated fenceScope

def _root_.Pop.SystemState.blockedOnRequests (state : SystemState) : List Request := Id.run do
  let fences := state.requests.filter Request.isFenceLike
  let mut res := []
  for fence in fences do
    -- All fences block on reads (this implies acq does not block on preds)
    unless allReadsDone state fence do
      res := res ++ [fence]
      continue
    -- Rel fences also block on writes/preds
    if fence.isGeqRel && !(memPredsDone state fence) then
      res := res ++ [fence]
      continue
  return res

  /- ∩
  r -> / Acq -> r/w; r/w -> acqrel r/w except (w -> r); r/w -> rel -> w
  -/
def propagateConstraintsAux (state : SystemState) (req : Request) (blocking : List Request) : Bool :=
  if blocking.isEmpty then
    true else
  if !req.isMem then -- fences don't propagate
    false else
  if req.isRead then blocking.all λ fenceLike =>
      (!fenceLike.isGeqAcq || allReadsDone state fenceLike) &&
      (!fenceLike.isFenceSC || memPredsDone state fenceLike)
 else if req.isWrite then blocking.all λ fenceLike =>
      (!fenceLike.isGeqAcq || allReadsDone state fenceLike) &&
      (!fenceLike.isGeqRel || memPredsDone state fenceLike)
 else panic! s!"unknown request type ({req})"

def propagateConstraints (state : SystemState) (rid : RequestId) (_ : ThreadId) : Bool :=
    let req := state.requests.getReq! rid
    let blocking := state.blockedOnRequests.filter
        λ r => r.thread == req.thread &&
        state.orderConstraints.lookup (state.scopes.reqThreadScope req) r.id req.id
    --dbg_trace "propagate {rid}, \n{blocking} not blocked? {propagateConstraintsAux state req blocking}"
    propagateConstraintsAux state req blocking

def addNewPredecessors (state : SystemState) (write read : Request) (thId : ThreadId) : SystemState := Id.run do
  if write.isWrite && read.isRead && write.address? == read.address? &&
  morallyStrong state.scopes write read && read.thread == thId then -- only reads at that thread
    return state.updateRequest $ write.makePredecessorAt thId
  else
    return state

def propagateEffects (state : SystemState) (reqId : RequestId) (thId : ThreadId)
: SystemState := Id.run do
  -- add predecessors as soon as RF edge formed
  let req := state.requests.getReq! reqId
  let mut res := state
  let successors := state.orderConstraints.successors (state.scopes.jointScope req.thread thId) reqId state.seen
  for reqId' in successors do
    if let some req' := state.requests.getReq? reqId' then
      res := addNewPredecessors res req req' thId
  return res
/-
 * A predecessor should behave *as if* it was in that same thread.
 * We add edge between predecessor and fence always (?):  maybe only for ≥release?
 * Add predecessor only at RF (not at propagate)
-/
def acceptEffects (state : SystemState) (reqId : RequestId) (thId : ThreadId) := Id.run do
  let writesOnThread := state.requests.filter λ w => w.isWrite && w.propagatedTo thId
  let mut st := state
  for write in writesOnThread do
    st := addNewPredecessors st write (state.requests.getReq! reqId) thId
  return st

instance : Arch where
  req := instArchReq
  propagateConstraints := propagateConstraints
  orderCondition := order
  scopeIntersection := scopeIntersection
  acceptEffects := acceptEffects
  propagateEffects := propagateEffects

namespace Litmus
def mkRead (scope_sem : String ) (addr : Address) (_ : String) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.read rr
              {scope := Scope.sys, sem := Semantics.rlx}
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
      {scope := scope, sem := sem}
    | _ =>
      dbg_trace "malformed PTX read request: W.{scope_sem}"
      BasicRequest.read rr default

def mkWrite (scope_sem : String) (addr : Address) (val : Value) (_ : String) : BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := val}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.write wr
              {scope := Scope.sys, sem := Semantics.rlx}
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
      BasicRequest.write wr {scope := scope, sem := sem}
    | _ =>
      dbg_trace "malformed PTX read request: W.{scope_sem}"
      BasicRequest.write wr default

def mkFence (scope_sem : String) (_ : String) : BasicRequest :=
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.fence
              {scope := Scope.sys, sem := Semantics.sc}
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
      BasicRequest.fence {scope := scope, sem := sem}
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
  alloyName := alloyName
  toAlloy := toAlloy

end Litmus
