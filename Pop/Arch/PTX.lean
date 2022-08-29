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
  deriving BEq

def Req.isStrong (req : Req) : Bool :=
  match req.sem with
  | .weak => false
  | _ => true

instance : Inhabited Req where default := { scope := Scope.sys, sem := Semantics.sc}

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
  | sem, scope => s!"{sem}.{scope}"

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

def scopeInclusive {V : ValidScopes} : Request → Request → Bool
  | r₁, r₂ =>
  let (t₁,t₂) := (r₁.thread, r₂.thread)
  let scope₁ := requestScope V r₁
  let scope₂ := requestScope V r₂
  scope₁.threads.contains t₂ && scope₂.threads.contains t₁

def _root_.Pop.Request.sem (req : Request) : Semantics :=
  req.basic_type.type.sem

-- some shortcuts
def _root_.Pop.Request.isFenceSC (req : Request) : Bool :=
  req.isBarrier && req.basic_type.type.sem == Semantics.sc

def _root_.Pop.Request.isFenceAcqRel (req : Request) : Bool :=
  req.isBarrier && req.basic_type.type.sem == Semantics.acqrel

def _root_.Pop.Request.isRel (req : Request) : Bool :=
  req.isWrite && req.basic_type.type.sem == Semantics.rel

def _root_.Pop.Request.isAcq (req : Request) : Bool :=
  req.isRead && req.basic_type.type.sem == Semantics.acq

infixl:85 "b⇒" => λ a b => !a || b

/-
  not scope_inclusive[r_old,r_new] or
  {
     // fence rel_acq : kindof like dmb_ld.
     // Reorder (w/ memory events): not allow if same thread, allowed otherwise
    	r_old + r_new in fence_acq_rel  => r_ord.thread != r_new.thread
    	r_old not in fence_sc
    	r_new not in fence_sc
    	(r_old + r_new) in (memory_access - thread_id.read_response)
  	  => r_old.addr != r_new.addr
  	r_new in ld_acquire and r_old in st_release => r_new.addr != r_old.addr
  	r_new in ld_acquire => r_new.thread != r_old.thread
  	r_new not in st_release
  }
-/
def reorder : ValidScopes → Request → Request → Bool
  | _, r_old, r_new =>
  let acqrel_fences := (r_old.isFenceAcqRel || r_new.isFenceAcqRel)
                       b⇒ (r_old.thread != r_new.thread)
  let sc_fences := !r_old.isFenceSC && !r_new.isFenceSC
  let satisfied := (r_new.isMem && !r_new.isSatisfied
                    && r_old.isMem && !r_old.isSatisfied)
                    b⇒ (r_new.address? != r_old.address?)
  let relacq := (r_new.isAcq && r_old.isRel) b⇒ (r_new.address? != r_old.address?)
  let acqthread := r_new.isAcq b⇒ (r_new.thread != r_old.thread)
  let newrel := !r_new.isRel
  --dbg_trace "[reorder] {r_old} {r_new}"
  --dbg_trace "[reorder] scope inclusive: {(@scopeInclusive V) r_old r_new}"
  --dbg_trace "[reorder] sc_fences : {sc_fences}"
  --dbg_trace "[reorder] satisfied : {satisfied}"
  --dbg_trace "[reorder] relacq : {relacq}"
  --dbg_trace "[reorder] acqthread : {acqthread}"
  --dbg_trace "[reorder] newrel : {newrel}"
  --dbg_trace "[reorder] acqrel_fences : {acqrel_fences}"
  --(@scopeInclusive V) r_old r_new ||
  (sc_fences && satisfied && relacq && acqthread && newrel && acqrel_fences)

instance : Arch where
  req := instArchReq
  acceptConstraints := λ _ _ _ => true
  propagateConstraints := λ _ _ _ => true
  satisfyReadConstraints := λ _ _ _ => true
  reorderCondition :=  reorder
  requestScope := requestScope

namespace Litmus
def mkRead (scope_sem : String ) (addr : Address) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.read rr {scope := Scope.sys, sem := Semantics.rlx}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          dbg_trace "invalid PTX scope: {scopeStr}"
          Scope.sys
      let sem := match semStr with
        | "acq" => Semantics.acq
        | "rlx" => Semantics.rlx
        | "weak" => Semantics.weak
        | _ =>
          dbg_trace "invalid PTX semantics: {semStr}"
          Semantics.weak
      BasicRequest.read rr {scope := scope, sem := sem}
    | _ =>
      dbg_trace "malformed PTX read request: W.{scope_sem}"
      BasicRequest.read rr default

def mkWrite (scope_sem : String) (addr : Address) (val : Value) : BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := val}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.write wr {scope := Scope.sys, sem := Semantics.rlx}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          dbg_trace "invalid PTX scope: {scopeStr}"
          Scope.sys
      let sem := match semStr with
        | "rel" => Semantics.rel
        | "rlx" => Semantics.rlx
        | "weak" => Semantics.weak
        | _ =>
          dbg_trace "invalid PTX semantics: {semStr}"
          Semantics.weak
      BasicRequest.write wr {scope := scope, sem := sem}
    | _ =>
      dbg_trace "malformed PTX read request: W.{scope_sem}"
      BasicRequest.write wr default

def mkBarrier (scope_sem : String) : BasicRequest :=
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.barrier {scope := Scope.sys, sem := Semantics.sc}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          dbg_trace "invalid PTX scope: {scopeStr}"
          Scope.sys
      let sem := match semStr with
        | "sc" => Semantics.sc
        | "acqrel" => Semantics.acqrel
        | _ =>
          dbg_trace "invalid PTX semantics: {semStr}"
          Semantics.sc
      BasicRequest.barrier {scope := scope, sem := sem}
    | _ =>
      dbg_trace "malformed PTX read request: Fence.{scope_sem}"
      BasicRequest.barrier default

-- Pretty hacky! Probably need nice syntax to configure this in the future
def mkInitState (n : Nat) :=
  match n with
  --| 2 =>
  --| 4 =>
  | _ =>
  let valid_scopes : ValidScopes :=
    { system_scope := List.range n, scopes := ListTree.leaf (List.range n)}
  SystemState.init valid_scopes


instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkBarrier := mkBarrier

def IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
def IRIW_3ctas := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} }
def IRIW_3ctas_1scoped_w := {| W. cta_rlx x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} }
def IRIW_3ctas_1scoped_r := {| W x=1 ||  R. cta_rlx x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} }
def IRIW_3ctas_scoped_rs_after := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R. cta_rlx y // 0 || R y // 1; Fence. cta_sc; R. cta_rlx x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} }

def IRIW_2ctas := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0, T2}, {T1, T3} }
def IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
def MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
def MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |}
def MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |}
def MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|}
def N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |}
def dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |}
def dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |}

def WRC := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|}
def WRC_two_deps := {| W x=1 || R. sys_acq x // 1;dep W y = 1 || R y // 1 ;dep R x // 0|}
def WRC_rel := {| W. sys_rel x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|}
def WRC_acq := {| W x=1 || R. sys_acq x // 1; W y = 1 || R. sys_acq y // 1 ;dep R x // 0|}
def WRC_no_dep := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ; R x // 0|}

def ptx_2 := [MP,MP_fence1,MP_fence2,MP_fence, N7, dekkers, dekkers_fence]
def ptx_3 := [WRC, WRC_rel, WRC_no_dep, WRC_acq, WRC_two_deps]

def ptx_4 := [IRIW, IRIW_3ctas, IRIW_3ctas_1scoped_w, IRIW_3ctas_1scoped_r, IRIW_3ctas_scoped_rs_after,  IRIW_2ctas, IRIW_fences]

def allPTX : List Litmus.Test := ptx_2 ++ ptx_3 ++ ptx_4
end Litmus
