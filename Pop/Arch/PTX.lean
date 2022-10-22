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
  let fences := (r_old.isFence && r_new.isFence)
                       && (r_old.thread == r_new.thread)
  /-
  r -> / Acq -> r/w; r/w -> acqrel r/w except (w -> r); r/w -> rel -> w
  -/
  let acqafter := r_old.isGeqAcq && (r_new.thread == r_old.thread)
  let samemem_reads := r_old.address? == r_new.address? && r_old.isRead && r_new.isRead
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
      λ r => r.isPredecessorAt fence.thread
    res := res ++ preds
  return res

def reqRFEstablishedScope (state : SystemState) (fenceLike : Request) (r : Request) : Bool :=
    let scope := scopeIntersection state.scopes r fenceLike
    let precidingWrites := filterNones $ state.orderConstraints.predecessors scope r.id state.seen |>.map
        λ predId => match state.requests.getReq? predId with
          | none => none
          | some req => if req.isWrite then
              some req else
              none
    --let rscope := state.scopes.intersection (PTX.requestScope state.scopes r) scope
    --dbg_trace "RF Established scope {fenceLike.id}? {(r :: precidingWrites).map (λ w => (w.id, w.fullyPropagated scope))}"
    state.isSatisfied r.id || (r :: precidingWrites).all (λ w => w.fullyPropagated scope)


def _root_.Pop.SystemState.blockedOnRequests (state : SystemState) : List RequestId := Id.run do
  let fences := state.requests.filter Request.isFenceLike
  let mut res := []
  for fence in fences do
    let preds := state.blockedOnFencePreds fence
    let scope := PTX.requestScope state.scopes fence
    -- This is the change, blocking when unsatisfied reads (breaks MP_fence_cta_1fence)
    let readsOnThread := state.requests.filter λ r => r.isRead &&  r.thread == fence.thread
    unless readsOnThread.all (reqRFEstablishedScope state fence) do
      res := res ++ [fence.id]
      continue
    unless !fence.isFenceSC || preds.all λ p => p.fullyPropagated scope do
       res := res ++ [fence.id]
  return res

def propagateConstraintsAux (state : SystemState) (req : Request) (reqs : List RequestId) : Bool :=
    match reqs with
      | [] =>
        let th_scope := state.scopes.jointScope req.thread req.thread
        let fences := state.requests.filter λ f => f.isFenceSC && f.thread == req.thread && state.orderConstraints.lookup th_scope f.id req.id
        fences.all λ r =>  r.fullyPropagated (requestScope state.scopes r)
      | blockId::rest =>
        let th_scope := state.scopes.jointScope req.thread req.thread
        let block := state.requests.getReq! blockId
        if block.isFenceSC && block.id != req.id then
          false
        else if block.thread != req.thread then
          propagateConstraintsAux state req rest
        else
          let readsOnThread := state.requests.filter λ r => r.isRead &&  r.thread == req.thread && r.id != req.id && !(state.orderConstraints.lookup th_scope block.id r.id)
          --dbg_trace "req {blockId} blocks propagate of {req.id} through reads {readsOnThread}? {readsOnThread.all (reqRFEstablishedScope state block)}"
          -- [1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 3, 4, 1, 1, 1]
          readsOnThread.all (reqRFEstablishedScope state block) && propagateConstraintsAux state req rest
            --(r.fullyPropagated scope && (precedingWrites state r scope).all λ pred => pred.fullyPropagated scope)

--def acceptConstraints (state : SystemState) (br : BasicRequest) (tid : ThreadId) : Bool :=
--    acceptConstraintsAux state br tid state.blockedOnRequests

def propagateConstraints (state : SystemState) (rid : RequestId) (_ : ThreadId) : Bool :=
  let req := state.requests.getReq! rid
  -- TODO: is this redundant with the propagateConstraintsAux?
  let prev := state.requests.filter λ p => p.thread == req.thread && p.id != rid
  let prev_propagated := state.scopes.containThread req.thread |>.all
    (λ scope => prev.all
      (λ p => !(state.orderConstraints.lookup scope p.id rid) || p.fullyPropagated scope))
  let blocking := state.blockedOnRequests.removeAll (prev.map Request.id)
  let not_blocked := propagateConstraintsAux state req blocking
  --dbg_trace "propagate {rid}, prev: {prev}, propagated? {prev_propagated}, {blocking} not blocked? {not_blocked}"
  prev_propagated && not_blocked
   -- state.blockedOnRequests.all
   -- λ fenceId =>
   --   let fence := state.requests.getReq! fenceId
   --   let scope := PTX.requestScope state.scopes fence
   --   if fence.isFenceSC && scope.threads.contains thId then
   --     let preds := state.blockedOnFencePreds fence |>.map Request.id
   --     let req := state.requests.getReq! rid
   --     preds.contains rid || (req.isRead && req.thread == fence.thread)
   --   else true

def addNewPredecessors (state : SystemState) (write read : Request) (thId : ThreadId) : SystemState := Id.run do
  if write.isWrite && read.isRead &&
  morallyStrong state.scopes write read && read.thread == thId then -- only reads at that thread
    return state.updateRequest $ write.makePredecessorAt thId
  else
    return state

-- TODO: somehow when we make a predecessor we need to add the edges immediately as well
-- see: WRC_acqrel [1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 1, 2] should have an edge 6[W. sys_rel y = 1] -> 5[R. sys_acq x]
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

end Litmus
