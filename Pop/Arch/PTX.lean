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
  | dep
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
  | .dep => "dep"

instance : ToString Scope where toString := Scope.toString
instance : ToString Semantics where toString := Semantics.toString

def Req.toString (req : Req) : String :=
  match req.sem, req.scope with
  | .rlx, .sys => ""
  | sem, scope => s!"{scope}_{sem}"

instance : ToString Req where toString := Req.toString


def reqBlockingSemantics (req : Req) : BlockingSemantics :=
  match req.sem with
    | .rlx => []
    | .weak => []
    | .rel => [.Read2WritePred, .Write2Write]
    | .acq => [.Read2ReadNoPred, .Read2WriteNoPred]
    | .acqrel => [.Read2WritePred, .Write2Write, .Read2ReadNoPred]
    | .sc => [.Read2WritePred, .Write2Write, .Read2ReadPred, .Write2Read]
    | .dep => [.Read2ReadNoPred, .Read2WriteNoPred]

instance : ArchReq where
  type := PTX.Req
  instBEq := PTX.instBEqReq
  instInhabited := PTX.instInhabitedReq
  isPermanentRead := λ _ => false
  instToString := PTX.instToStringReq

def toAlloy : String → BasicRequest → String
    | moduleName, .read _ ty =>
      let pref := if moduleName == "cmm" then "ptx" else "" -- hacky...
      match ty.sem with
        | .acq => moduleName ++ "/Acquire"
        | _ => moduleName ++ s!"/{pref}Read - {moduleName}/Acquire"
    | moduleName, .write _ ty =>
      let pref := if moduleName == "cmm" then "ptx" else ""
      match ty.sem with
        | .rel => moduleName ++ "/Release"
        | _ => moduleName ++ s!"/{pref}Write - {moduleName}/Release"
    | moduleName, .fence ty =>
      let pref := if moduleName == "cmm" then "ptx" else ""
      match ty.sem with
        | .sc => moduleName ++ s!"/{pref}FenceSC"
        | .acqrel => moduleName ++ s!"/{pref}FenceAcqRel"
        | .rel => moduleName ++ s!"/{pref}FenceRel"
        | .acq => moduleName ++ s!"/{pref}FenceAcq"
        | _ => moduleName ++ s!"/UnknownFence"
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

def Request.markedScope (req : Request) : PTX.Scope :=
  req.basic_type.type.scope

-- some shortcuts
def Request.isFenceSC (req : Request) : Bool :=
  req.isFence && req.basic_type.type.sem == PTX.Semantics.sc

def Request.isFenceAcqRel (req : Request) : Bool :=
  req.isFence && req.basic_type.type.sem == PTX.Semantics.acqrel

def Request.isRel (req : Request) : Bool :=
  req.basic_type.type.sem == PTX.Semantics.rel

def Request.isDep (req : Request) : Bool :=
  req.isFence && req.basic_type.type.sem == PTX.Semantics.dep

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

def Request.isPTXFenceLike (req : Request) : Bool :=
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
    return intersection.get!

def scopesMatch : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
    let scope := scopeIntersection V r_old r_new |>.threads
    scope.contains r_old.thread && scope.contains r_new.thread

/-
r -> / Acq -> r/w; r/w -> acqrel r/w except (w -> r); r/w -> rel -> w
-/
def order : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
  let samemem_reads := r_old.address? == r_new.address? && r_old.isRead && r_new.isRead
  let acqafter := r_old.isGeqAcq && (r_new.thread == r_old.thread)
  let acqread :=  r_new.isGeqAcq && (r_new.thread == r_old.thread && r_old.isRead)
  let newrel := r_new.isGeqRel && (r_new.thread == r_old.thread || r_old.isPredecessorAt r_new.thread)
  let relwrite := r_old.isGeqRel && r_new.thread == r_old.thread && r_new.isWrite
  let dep_old := r_old.isDep && r_new.isMem && r_new.thread == r_old.thread
  let dep_new := r_new.isDep && r_old.isRead && r_new.thread == r_old.thread
  let pred := r_old.isPredecessorAt r_new.thread && r_new.isGeqRel
  -- TODO: what about acqrel and (w -> r)?
   -- dbg_trace "[order] {r_old} {r_new}"
   -- dbg_trace "[order] acqafter : {acqafter}"
   -- dbg_trace "[order] acqread : {acqread}"
   -- dbg_trace "[order] newrel : {newrel}"
   -- dbg_trace "[order] relwrite : {relwrite}"
   -- dbg_trace "[order] scopes match: {scopesMatch V r_old r_new}"
  scopesMatch V r_old r_new &&
  (acqafter || newrel || acqread || relwrite || pred || samemem_reads || dep_old || dep_new)

def blockingSemantics : Request → BlockingSemantics
    | req => reqBlockingSemantics req.basic_type.type

 def predecessorConstraints : SystemState → RequestId → RequestId → Bool
   | state, writeId, readId =>
       match (state.requests.getReq? writeId), (state.requests.getReq? readId) with
         | some write, some read => morallyStrong state.scopes write read
         | _, _ => false

instance : Arch where
  req := instArchReq
  orderCondition := order
  scopeIntersection := scopeIntersection
  blockingSemantics := blockingSemantics
  predecessorConstraints  := predecessorConstraints

namespace Litmus
def mkRead (scope_sem : String ) (addr : Address) (_ : String) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none, atomicity := .nonatomic}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.read rr
              {scope := Scope.sys, sem := Semantics.rlx}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          panic! s!"(read) invalid PTX scope: {scopeStr}"
      let sem := match semStr with
        | "acq" => Semantics.acq
        | "rlx" => Semantics.rlx
        | "weak" => Semantics.weak
        | _ =>
          panic! s!"(read) invalid PTX semantics: {semStr}"
      BasicRequest.read rr
      {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed PTX read request: W.{scope_sem}"

def mkWrite (scope_sem : String) (addr : Address) (val : Value) (_ : String) : BasicRequest :=
  let wr : WriteRequest := match val with
    | some v => { addr := addr, val := .const v, atomicity := .nonatomic}
    | none => { addr := addr, val := .failed, atomicity := .nonatomic}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.write wr
              {scope := Scope.sys, sem := Semantics.rlx}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          panic! s!"(write) invalid PTX scope: {scopeStr}"
      let sem := match semStr with
        | "rel" => Semantics.rel
        | "rlx" => Semantics.rlx
        | "weak" => Semantics.weak
        | _ =>
          panic! s!"(write) invalid PTX semantics: {semStr}"
      BasicRequest.write wr {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed PTX read request: W.{scope_sem}"

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
          panic! s!"(fence) invalid PTX scope: {scopeStr}"
      let sem := match semStr with
        | "sc" => Semantics.sc
        | "acqrel" => Semantics.acqrel
        | "rel" => Semantics.rel
        | "acq" => Semantics.acq
        | "dep" => Semantics.dep
        | _ =>
          panic! s!"(fence) invalid PTX semantics: {semStr}"
      BasicRequest.fence {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed PTX read request: Fence.{scope_sem}"

def mkRMW (_ : String) (addr: Address) (_ : String) : BasicRequest × BasicRequest :=
  dbg_trace "unipmelmented RMWs in PTX"
  let wr : WriteRequest := { addr := addr, val := .fetchAndAdd, atomicity := .transactional}
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none, atomicity := .transactional}
  (BasicRequest.read rr default, BasicRequest.write wr default)

def mkInitState (n : Nat) :=
  match n with
  | _ =>
  let valid_scopes : ValidScopes :=
    { system_scope := List.range n, scopes := ListTree.leaf (List.range n)}
      --scopes_consistent := sorry, system_scope_is_scope := sorry}
  SystemState.init valid_scopes

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkRMW := mkRMW
  mkFence := mkFence
  alloyName := alloyName
  toAlloy := toAlloy

end Litmus
