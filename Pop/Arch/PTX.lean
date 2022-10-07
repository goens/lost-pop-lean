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
  let typeStr :=
    match req.sem, req.scope with
    | .rlx, .sys => ""
    | sem, scope => s!"{sem}.{scope}"
  let predStr :=
    match req.predecessorAt with
      | [] => ""
      | preds => s!" pred @ {preds}"
  typeStr ++ predStr

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
  req.basic_type.type.sem == PTX.Semantics.acqrel

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

infixl:85 "b⇒" => λ a b => !a || b

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

def reorder : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
  -- TODO: we are not sure if this might make our model stronger than necessary
  let fences := (r_old.isFence && r_new.isFence)
                       b⇒ (r_old.thread != r_new.thread)
  -- Removing 'satisfied': PTX doesn't keep any reads
  -- Removing 'relacq': redundant with RF/FR edges; we don't see the point
  -- TODO: is SC fence also rel/acq?
  -- TODO: Discuss this
  /-
  r -> / Acq -> r/w; r/w -> acqrel r/w except (w -> r); r/w -> rel -> w
  -/
  let acqafter := r_old.isGeqAcq b⇒ (r_new.thread != r_old.thread)
  let acqread :=  r_new.isGeqAcq b⇒ (r_new.thread != r_old.thread && r_old.isRead)
   -- TODO: why also for diff. threads? should this be handled with predeecessors?
  let newrel := !r_new.isGeqRel
  let relwrite := r_old.isGeqRel b⇒ (r_new.thread != r_old.thread && r_new.isWrite)
  -- TODO: what about acqrel and (w -> r)?
  -- dbg_trace "[reorder] {r_old} {r_new}"
  -- dbg_trace "[reorder] fences : {fences}"
  -- dbg_trace "[reorder] satisfied : {satisfied}"
  -- dbg_trace "[reorder] relacq : {relacq}"
  -- dbg_trace "[reorder] relafter : {relbefore}"
  -- dbg_trace "[reorder] acqbefore : {acqafter}"
  -- dbg_trace "[reorder] newrel : {newrel}"
  -- dbg_trace "[reorder] !scopes match: {!scopesMatch V r_old r_new}"
  !scopesMatch V r_old r_new ||
  (acqafter  && newrel && fences && acqread && relwrite)

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

def _root_.Pop.SystemState.blockedOnFence (state : SystemState) : Option RequestId := Id.run do
  let fences := state.requests.filter Request.isFence
  for fence in fences do
    let preds := state.blockedOnFencePreds fence
    let scope := PTX.requestScope state.scopes fence
    -- This is the change, blocking when unsatisfied reads (breaks MP_fence_cta_1fence)
    -- let readsOnThread := state.requests.filter λ r => r.isRead &&  r.thread == fence.thread
    -- unless readsOnThread.all λ r => state.isSatisfied r.id do
    --   --dbg_trace "blocked on Fence (R{fence.id}) with unsatisfied reads ({readsOnThread}) "
    --   return some fence.id
    unless !fence.isFenceSC || preds.all λ p => p.fullyPropagated scope do
      --dbg_trace "blocked on FenceSC (R{fence.id}) with unpropagated predecessors ({preds}) to scope {scope}"
      return some fence.id
  return none

def acceptConstraints (state : SystemState) (br : BasicRequest) (tid : ThreadId) : Bool :=
    match state.blockedOnFence with
      | none =>
        let scfences := state.requests.filter Request.isFenceSC
        scfences.all λ r =>  r.thread != tid || r.fullyPropagated (requestScope state.scopes r)
      | some fenceId =>
        let fence := state.requests.getReq! fenceId
        if fence.isFenceSC then
           false
        else
           true --br.isWrite

def propagateConstraints (state : SystemState) (rid : RequestId) (thId : ThreadId) : Bool :=
  if let some fenceId := state.blockedOnFence then
    let fence := state.requests.getReq! fenceId
    let scope := PTX.requestScope state.scopes fence
    if fence.isFenceSC && scope.threads.contains thId then
      let preds := state.blockedOnFencePreds fence |>.map Request.id
      let req := state.requests.getReq! rid
      preds.contains rid || (req.isRead && req.thread == fence.thread)
    else true
  else
    true

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
: SystemState :=
  let readsFrom := state.satisfied.lookup reqId
  match readsFrom with
    | none => state
    | some writeId =>
      let write := state.requests.getReq? writeId |>.get!
      let read := state.requests.getReq? reqId |>.get!
      --dbg_trace "checking wether to add Req.{writeId} as predecessor to T{thId}"
      --dbg_trace "MS:{morallyStrong state.scopes read write}, prop: {!(write.propagated_to.elem thId)}"
      -- TODO: move this to satisfyEffects
      if (morallyStrong state.scopes read write) && !(write.propagated_to.elem thId)
      then
        state.updateRequest $ write.makePredecessorAt thId
      else
        state

/-
 * A predecessor should behave *as if* it was in that same thread.
 * We add edge between predecessor and fence always (?):  maybe only for ≥release?
 * Add predecessor only at RF (not at propagate)
-/
def acceptEffects (state : SystemState) (reqId : RequestId) (thId : ThreadId) :=
  let propState := propagateEffects state reqId thId
  if (state.requests.getReq! reqId).isFence then addEdgesOnFence propState else propState

instance : Arch where
  req := instArchReq
  acceptConstraints := acceptConstraints
  propagateConstraints := propagateConstraints
  reorderCondition := reorder
  requestScope := requestScope
  acceptEffects := acceptEffects
  propagateEffects := propagateEffects

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

deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |} ✓
deflitmus IRIW_3ctas := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } 𐄂
deflitmus IRIW_4ctas := {| W x=1 ||  R. cta_rlx x // 1 ; Fence. sys_sc;  R. cta_rlx y // 0 || R. cta_rlx y // 1; Fence. sys_sc; R. sys_rlx x // 0 || W y=1 |}
  where sys := { {T0}, {T1}, {T2}, {T3} } ✓

deflitmus IRIW_3ctas_1scoped_w := {| W. cta_rlx x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ✓
deflitmus IRIW_3ctas_1scoped_r := {| W x=1 ||  R. cta_rlx x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ✓
deflitmus IRIW_3ctas_scoped_rs_after := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R. cta_rlx y // 0 || R y // 1; Fence. cta_sc; R. cta_rlx x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } 𐄂

deflitmus IRIW_2ctas := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0, T2}, {T1, T3} } ✓
deflitmus IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |} 𐄂
deflitmus IRIW_sc_acq_fence := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence. sys_acqrel; R x // 0 || W y=1 |} ✓

deflitmus simpleRF := {| W. cta_rlx x=1 || R. cta_rlx x // 1 |}
  where sys := { {T0}, {T1} } ✓
deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |} ✓
deflitmus MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |} ✓
deflitmus MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |} ✓
deflitmus MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|} 𐄂
deflitmus MP_fence_cta := {| W x=1; Fence. cta_sc; W y=1 ||  R y // 1; Fence. cta_sc; R x // 0|}
  where sys := { {T0}, {T1} } ✓
deflitmus MP_read_cta := {| W x=1; Fence. sys_sc; W y=1 ||  R. cta_rlx y // 1; Fence. sys_sc; R x // 0|}
  where sys := { {T0}. ptx, {T1}. x86} 𐄂
deflitmus MP_fence_consumer_weak := {| W. sys_weak x=1; Fence. sys_sc; W y=1 ||  R y // 1; Fence. sys_sc; R. sys_weak x // 0|} -- 𐄂
deflitmus MP_fence_weak := {| W. sys_weak x=1; Fence. sys_sc; W. sys_weak y=1 ||  R. sys_weak y // 1; Fence. sys_sc; R. sys_weak x // 0|} -- 𐄂
deflitmus MP_fence_weak_rel_acq := {| W. sys_weak x=1; Fence. sys_rel; W. sys_weak y=1 ||  R. sys_weak y // 1; Fence. sys_acq; R. sys_weak x // 0|} -- 𐄂
deflitmus MP_fence_rel_acq := {| W x=1; Fence. sys_rel; W  y=1 ||  R y // 1; Fence. sys_acq; R x // 0|} 𐄂  -- [2, 2, 2, 3, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1] →  [Accept (W x(1)), Accept (Fence.rel.sys), Accept (W y(1)), Propagate Req4 (W y(1)) to Thread 1, Accept (R y), Accept (Fence.acq.sys), Propagate Req6 (Fence.acq.sys) to Thread 0, Accept (R x), Propagate Req7 (R x(0)) to Thread 0, Propagate Req2 (W x(1)) to Thread 1, Propagate Req3 (Fence.rel.sys) to Thread 1, Satisfy Req7 (R x(0)) with Req0 (W x(0)), Propagate Req5 (R y(1)) to Thread 0, Satisfy Req5 (R y(1)) with Req4 (W y(1))]
/- The issue with this test seems to be with the checking of the reorder condition when updating the order constraints:
  when accepting a new request r_new we check reorder r_new r_old, whereas when propagating, we check reorder r_old r_new.
  In this way, by delaying the acceptance of the acquire fence, it avoids getting ordered with the release fence. This
  can in turn be leveraged to propagate the acquire fence first, effectively avoiding the ordering.
  -/
deflitmus MP_rel_acq := {| W x=1; W. sys_rel y=1 ||  R. sys_acq y // 1; R x // 0|} 𐄂
deflitmus MP_fence_cta_1fence := {| W x=1; Fence. sys_sc; W y=1 ||  R y // 1; Fence. cta_sc; R x // 0|}
  where sys := { {T0}, {T1} } ✓
deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |} ✓
deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |}  ✓
deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |} 𐄂
deflitmus dekkers_acqrelfence := {| W x=1; Fence. sys_acqrel; R y //0 || W y=1; Fence. sys_acqrel;  R x // 0 |} ✓

deflitmus WRC := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|} ✓
deflitmus WRC_two_deps := {| W x=1 || R. sys_acq x // 1;dep W y = 1 || R y // 1 ;dep R x // 0|} ✓
deflitmus WRC_rel := {| W. sys_rel x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|} ✓
deflitmus WRC_acq := {| W x=1 || R. sys_acq x // 1; W y = 1 || R. sys_acq y // 1 ;dep R x // 0|} ✓
deflitmus WRC_no_dep := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ; R x // 0|} ✓
deflitmus WRC_cta_1_2 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0}, {T1, T2}} 𐄂
deflitmus WRC_cta_2_1 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0, T1}, {T2}} ✓
/-
[2, 2, 1, 7, 2, 6, 4, 4, 1, 5, 5, 2, 4, 1, 4] ??
 [Accept (R x),
  Accept (Fence.rel.sys),
  Accept (R.rlx.cta y),
  Propagate Req4 (R.rlx.cta y(1)) to Thread 1,
  Accept (W.rlx.cta y(1)),
  Propagate Req5 (W.rlx.cta pred @ [2] y(1)) to Thread 0,
  Propagate Req2 (R x(1)) to Thread 2,
  Propagate Req3 (Fence.rel.sys) to Thread 2,
  Accept (Fence.acq.sys),
  Propagate Req5 (W.rlx.cta pred @ [2] y(1)) to Thread 2,
  Propagate Req6 (Fence.acq.sys) to Thread 1,
  Accept (W x(1)),
  Propagate Req7 (W. pred @ [1] x(1)) to Thread 1,
  Accept (R x),
  Propagate Req8 (R x(0)) to Thread 1,
  Propagate Req4 (R.rlx.cta y(1)) to Thread 0,
  Propagate Req2 (R x(1)) to Thread 0,
  Propagate Req3 (Fence.rel.sys) to Thread 0,
  Satisfy Req4 (R.rlx.cta y(1)) with Req5 (W.rlx.cta pred @ [2] y(1)),
  Propagate Req6 (Fence.acq.sys) to Thread 0,
  Propagate Req8 (R x(0)) to Thread 0,
  Propagate Req7 (W. pred @ [1] x(1)) to Thread 2,
  Satisfy Req8 (R x(0)) with Req0 (W. pred @ [2] x(0)),
  Satisfy Req2 (R x(1)) with Req7 (W. pred @ [1] x(1))] -/
deflitmus WRC_cta_2_1' := {| W. cta_rlx x=1 || R. cta_rlx x // 1; Fence. sys_rel; W. sys_rlx y = 1 || R. sys_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0, T1}, {T2}} 𐄂
deflitmus WRC_cta_1_1_1 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0}, {T1}, {T2}} ✓

deflitmus WWRWRR := {| W. cta_rel x=1;  W. cta_rel y=1 || R. cta_acq y // 1; W. cta_rel z = 1 || R. cta_acq z // 1 ; R. cta_acq x // 0|} 𐄂
deflitmus WWRWRR_scoped := {| W. cta_rel x=1;  W. cta_rel y=1 || R. cta_acq y // 1; W. cta_rel z = 1 || R. cta_acq z // 1 ; R. cta_acq x // 0|}
  where sys := { {T0}, {T1, T2}} 𐄂

deflitmus three_vars_ws := {| W x = 1; Fence. sys_acqrel; W y = 1 || W y = 2; Fence. sys_acqrel; W z = 1 || R z // 1; Fence. sys_acqrel; R x // 0 |} ✓
deflitmus two_plus_two2 := {| W. sys_rel x=1; W. sys_rel y=2;  R. sys_acq y // 1 || W. sys_rel y=1; W. sys_rel x=2 ;  R. sys_acq x // 1|} ✓
deflitmus co_two_thread := {| W x = 1; R x // 2 || W x = 2; R x // 1 |} ✓
deflitmus co_four_thread := {| W x = 1 || R x // 1 ; R x // 2 ||  R x // 2; R x // 1; W x = 2 |} 𐄂

deflitmus write_serialization := {| W. cta_rlx x=1;  W. cta_rlx x=2 || R. cta_rlx x // 1; R. cta_rlx x // 2 || R. cta_rlx x // 2 ; R. cta_rlx x // 1|}
  where sys := { {T0, T1}, {T2} } ✓
deflitmus write_serialization_unscoped := {| W. cta_rlx x=1;  W. cta_rlx x=2 || R. cta_rlx x // 1; R. cta_rlx x // 2 || R. cta_rlx x // 2 ; R. cta_rlx x // 1|} 𐄂


def allPTX : List Litmus.Test := litmusTests!
def ptx_2 := allPTX.filter λ lit => lit.numThreads == 2
def ptx_3 := allPTX.filter λ lit => lit.numThreads == 3
def ptx_4 := allPTX.filter λ lit => lit.numThreads == 4
end Litmus
