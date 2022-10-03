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
  req.isBarrier && req.basic_type.type.sem == PTX.Semantics.sc

def Request.isFenceAcqRel (req : Request) : Bool :=
  req.isBarrier && req.basic_type.type.sem == PTX.Semantics.acqrel

def Request.isRel (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.rel

def Request.isAcq (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.acq

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
  let fences := (r_old.isBarrier && r_new.isBarrier)
                       b⇒ (r_old.thread != r_new.thread)
  let satisfied := (r_new.isMem && !r_new.isSatisfied
                    && r_old.isMem && !r_old.isSatisfied)
                    b⇒ (r_new.address? != r_old.address?)
  let relacq := (r_new.isAcq && r_old.isRel) b⇒ (r_new.address? != r_old.address?)
  -- TODO: Discuss this
  -- Old idea was something about the originating threads being different:
  -- I'm not sure about this now...
  -- let acqthread := r_new.isAcq b⇒ (r_new.thread != r_old.thread) -- rel before, acq after
  -- Trying instead:
  let acqafter := r_old.isAcq b⇒ !(r_new.isRead || r_new.thread != r_old.thread)
  let relbefore := r_old.isWrite b⇒ !(r_new.isAcq || r_new.thread != r_old.thread)
  let newrel := !r_new.isRel
  -- dbg_trace "[reorder] {r_old} {r_new}"
  -- dbg_trace "[reorder] fences : {fences}"
  -- dbg_trace "[reorder] satisfied : {satisfied}"
  -- dbg_trace "[reorder] relacq : {relacq}"
  -- dbg_trace "[reorder] relafter : {relbefore}"
  -- dbg_trace "[reorder] acqbefore : {acqafter}"
  -- dbg_trace "[reorder] newrel : {newrel}"
  -- dbg_trace "[reorder] !scopes match: {!scopesMatch V r_old r_new}"
  !scopesMatch V r_old r_new ||
  (satisfied && relacq && acqafter && relbefore && newrel && fences)

-- On SC fence we propagate predecessors to the SC fence's scope. We enforce
-- this by not accepting, propagating or satisfying any other requests unless
-- this is propagated. This is the check we use for that. Returns the first
-- SC fence that it finds that it's blocked on (it should never be more than
-- one anyway)
private def _root_.Pop.SystemState.blockedOnSCFencePreds (state : SystemState) (fence : Request) : List Request := Id.run do
  let mut res := []
  let scope := PTX.requestScope state.scopes fence
  if fence.fullyPropagated scope then
    return res
  else
    let preds := state.requests.filter
      λ r => r.predecessorAt.contains fence.thread ||
             r.propagatedTo fence.thread && r.id != fence.id
    res := res ++ preds
  return res

def _root_.Pop.SystemState.blockedOnSCFence (state : SystemState) : Option RequestId := Id.run do
  let scfences := state.requests.filter Request.isFenceSC
  for fence in scfences do
    let preds := state.blockedOnSCFencePreds fence
    let scope := PTX.requestScope state.scopes fence
    unless preds.all λ p => p.fullyPropagated scope do
      --dbg_trace "blocked on R{fence.id}"
      return some fence.id
  return none

def acceptConstraints (state : SystemState) (_ : BasicRequest) (tid : ThreadId) : Bool :=
  let scfences := state.requests.filter Request.isFenceSC
  state.blockedOnSCFence == none &&
  scfences.all λ r =>  r.thread != tid || r.fullyPropagated (requestScope state.scopes r)

def propagateConstraints (state : SystemState) (rid : RequestId) (_ : ThreadId) : Bool :=
  if let some fenceId := state.blockedOnSCFence then
    let fence := state.requests.getReq! fenceId
    let preds := state.blockedOnSCFencePreds fence |>.map Request.id
    preds.contains rid
  else
    true

def satisfyReadConstraints (state : SystemState) ( _ _ : RequestId) : Bool :=
  state.blockedOnSCFence == none

-- on a (rel/acq/acqrel) fence we add an edge from each pred to this fence
-- according to the scopes-match table
def addEdgesOnFence (state : SystemState) : SystemState := Id.run do
  let fences := state.requests.filter λ r => r.isBarrier &&
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

def acceptEffects (state : SystemState) (br : BasicRequest) (_ : ThreadId) :=
  if br.isBarrier then addEdgesOnFence state else state

instance : Arch where
  req := instArchReq
  acceptConstraints := acceptConstraints
  satisfyReadConstraints := satisfyReadConstraints
  propagateConstraints := propagateConstraints
  reorderCondition := reorder
  requestScope := requestScope
  acceptEffects := acceptEffects
  propagateEffects := propagateEffects


namespace Litmus
def mkRead (scope_sem : String ) (addr : Address) : BasicRequest :=
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

def mkWrite (scope_sem : String) (addr : Address) (val : Value) : BasicRequest :=
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

def mkBarrier (scope_sem : String) : BasicRequest :=
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.barrier
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
      BasicRequest.barrier {scope := scope, sem := sem, predecessorAt := []}
    | _ =>
      dbg_trace "malformed PTX read request: Fence.{scope_sem}"
      BasicRequest.barrier default

def mkInitState (n : Nat) :=
  match n with
  | _ =>
  let valid_scopes : ValidScopes :=
    { system_scope := List.range n, scopes := ListTree.leaf (List.range n)}
  SystemState.init valid_scopes

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkBarrier := mkBarrier

deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |} ✓
deflitmus IRIW_3ctas := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ×
deflitmus IRIW_4ctas := {| W x=1 ||  R. cta_rlx x // 1 ; Fence. sys_sc;  R. cta_rlx y // 0 || R. cta_rlx y // 1; Fence. sys_sc; R. sys_rlx x // 0 || W y=1 |}
  where sys := { {T0}, {T1}, {T2}, {T3} } ✓

deflitmus IRIW_3ctas_1scoped_w := {| W. cta_rlx x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ✓
deflitmus IRIW_3ctas_1scoped_r := {| W x=1 ||  R. cta_rlx x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ✓
deflitmus IRIW_3ctas_scoped_rs_after := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R. cta_rlx y // 0 || R y // 1; Fence. cta_sc; R. cta_rlx x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ×

deflitmus IRIW_2ctas := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0, T2}, {T1, T3} } ✓
deflitmus IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |} ×
deflitmus IRIW_sc_acq_fence := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence. sys_acqrel; R x // 0 || W y=1 |} ✓

deflitmus simpleRF := {| W. cta_rlx x=1 || R. cta_rlx x // 1 |}
  where sys := { {T0}, {T1} } ✓
deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |} ✓
deflitmus MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |} ✓
deflitmus MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |} ✓
deflitmus MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|} ×
deflitmus MP_fence_cta := {| W x=1; Fence. cta_sc; W y=1 ||  R y // 1; Fence. cta_sc; R x // 0|}
  where sys := { {T0}, {T1} } ✓
deflitmus MP_read_cta := {| W x=1; Fence. sys_sc; W y=1 ||  R. cta_rlx y // 1; Fence. sys_sc; R x // 0|}
  where sys := { {T0}, {T1} } ×
deflitmus MP_fence_consumer_weak := {| W. sys_weak x=1; Fence. sys_sc; W y=1 ||  R y // 1; Fence. sys_sc; R. sys_weak x // 0|} -- ×
deflitmus MP_fence_weak := {| W. sys_weak x=1; Fence. sys_sc; W. sys_weak y=1 ||  R. sys_weak y // 1; Fence. sys_sc; R. sys_weak x // 0|} -- ×
deflitmus MP_fence_weak_rel_acq := {| W. sys_weak x=1; Fence. sys_rel; W. sys_weak y=1 ||  R. sys_weak y // 1; Fence. sys_acq; R. sys_weak x // 0|} -- ×
deflitmus MP_fence_rel_acq := {| W x=1; Fence. sys_rel; W  y=1 ||  R y // 1; Fence. sys_acq; R x // 0|} ×  -- [2, 2, 2, 3, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1] →  [Accept (W x(1)), Accept (Fence.rel.sys), Accept (W y(1)), Propagate Req4 (W y(1)) to Thread 1, Accept (R y), Accept (Fence.acq.sys), Propagate Req6 (Fence.acq.sys) to Thread 0, Accept (R x), Propagate Req7 (R x(0)) to Thread 0, Propagate Req2 (W x(1)) to Thread 1, Propagate Req3 (Fence.rel.sys) to Thread 1, Satisfy Req7 (R x(0)) with Req0 (W x(0)), Propagate Req5 (R y(1)) to Thread 0, Satisfy Req5 (R y(1)) with Req4 (W y(1))]
/- The issue with this test seems to be with the checking of the reorder condition when updating the order constraints:
  when accepting a new request r_new we check reorder r_new r_old, whereas when propagating, we check reorder r_old r_new.
  In this way, by delaying the acceptance of the acquire fence, it avoids getting ordered with the release fence. This
  can in turn be leveraged to propagate the acquire fence first, effectively avoiding the ordering.
  -/
deflitmus MP_rel_acq := {| W x=1; W. sys_rel y=1 ||  R. sys_acq y // 1; R x // 0|} ×
deflitmus MP_fence_cta_1fence := {| W x=1; Fence. sys_sc; W y=1 ||  R y // 1; Fence. cta_sc; R x // 0|}
  where sys := { {T0}, {T1} } ✓
deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |} ✓
deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |}  ✓
deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |} ×

deflitmus WRC := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|} ×
deflitmus WRC_two_deps := {| W x=1 || R. sys_acq x // 1;dep W y = 1 || R y // 1 ;dep R x // 0|} ×
deflitmus WRC_rel := {| W. sys_rel x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|} ×
deflitmus WRC_acq := {| W x=1 || R. sys_acq x // 1; W y = 1 || R. sys_acq y // 1 ;dep R x // 0|} ×
deflitmus WRC_no_dep := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ; R x // 0|} ✓
deflitmus WRC_cta_1_2 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0}, {T1, T2}} ×
deflitmus WRC_cta_2_1 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0, T1}, {T2}} ✓
deflitmus WRC_cta_2_1' := {| W. cta_rlx x=1 || R. cta_rlx x // 1; Fence. sys_rel; W. sys_rlx y = 1 || R. sys_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0, T1}, {T2}} ×
deflitmus WRC_cta_1_1_1 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0}, {T1}, {T2}} ✓

deflitmus WWRWRR := {| W. cta_rel x=1;  W. cta_rel y=1 || R. cta_acq y // 1; W. cta_rel z = 1 || R. cta_acq z // 1 ; R. cta_acq x // 0|} ×
deflitmus WWRWRR_scoped := {| W. cta_rel x=1;  W. cta_rel y=1 || R. cta_acq y // 1; W. cta_rel z = 1 || R. cta_acq z // 1 ; R. cta_acq x // 0|}
  where sys := { {T0}, {T1, T2}} ×

deflitmus three_vars_ws := {| W x = 1; Fence. sys_acqrel; W y = 1 || W y = 2; Fence. sys_acqrel; W z = 1 || R z // 1; Fence. sys_acqrel; R x // 0 |} ✓
deflitmus two_plus_two2 := {| W. sys_rel x=1; W. sys_rel y=2;  R. sys_acq y // 1 || W. sys_rel y=1; W. sys_rel x=2 ;  R. sys_acq x // 1|} ✓
deflitmus co_two_thread := {| W x = 1; R x // 2 || W x = 2; R x // 1 |} ✓
deflitmus co_four_thread := {| W x = 1 || R x // 1 ; R x // 2 ||  R x // 2; R x // 1; W x = 2 |} ×

deflitmus write_serialization := {| W. cta_rlx x=1;  W. cta_rlx x=2 || R. cta_rlx x // 1; R. cta_rlx x // 2 || R. cta_rlx x // 2 ; R. cta_rlx x // 1|}
  where sys := { {T0, T1}, {T2} } ✓
deflitmus write_serialization_unscoped := {| W. cta_rlx x=1;  W. cta_rlx x=2 || R. cta_rlx x // 1; R. cta_rlx x // 2 || R. cta_rlx x // 2 ; R. cta_rlx x // 1|} ×


def allPTX : List Litmus.Test := litmusTests!
def ptx_2 := allPTX.filter λ lit => lit.numThreads == 2
def ptx_3 := allPTX.filter λ lit => lit.numThreads == 3
def ptx_4 := allPTX.filter λ lit => lit.numThreads == 4
end Litmus
