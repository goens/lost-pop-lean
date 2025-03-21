-- Author(s): Andrés Goens, Fletch Rydell
-- See Copyright Notice in LICENSE

import Pop.States
import Pop.Litmus
import Pop.Util

open Pop Util

namespace ScopedRC

inductive Scope
  | gpu
  | sys
  deriving Inhabited, BEq, Repr

def Scope.intersection : Scope → Scope → Scope
  | .gpu, _ => gpu
  | .sys, s => s

infixl:85 "∩" => Scope.intersection

inductive Semantics
  | rel
  | acq
  | rlx
  deriving Inhabited, BEq, Repr

structure Req where
  (scope : Scope)
  (sem : Semantics)
  deriving BEq

instance : Inhabited Req where default :=
  { scope := Scope.sys, sem := Semantics.rlx}

def Scope.toString : Scope → String
  | .gpu => "gpu"
  | .sys => "sys"

def Semantics.toString : Semantics → String
  | .rel => "rel"
  | .acq => "acq"
  | .rlx => "rlx"

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
    | .rel => [.Read2WritePred, .Write2Write]
    | .acq => [.Read2ReadPred, .Read2WritePred]

instance : ArchReq where
  type := ScopedRC.Req
  instBEq := ScopedRC.instBEqReq
  instInhabited := ScopedRC.instInhabitedReq
  instToString := ScopedRC.instToStringReq

def getThreadScope (valid : ValidScopes) (thread : ThreadId) (scope : Scope) :=
  let containing := valid.containThread thread
  -- TODO: Could I get rid of this sorting (from the ListTree structure)?
    |>.toArray |>.qsort (λ l₁ l₂ => l₁.threads.length < l₂.threads.length)
  match scope with
  | .sys => valid.systemScope
  | .gpu => if let some gpu := containing[0]? -- TODO: check this
    then gpu
    else panic! "invalid gpu scope"

def requestScope (valid : ValidScopes) (req : Request) : @Pop.Scope valid :=
  getThreadScope valid req.thread req.basic_type.type.scope

def scopeInclusive (V : ValidScopes) (r₁ r₂ : Request) : Bool :=
  let (t₁,t₂) := (r₁.thread, r₂.thread)
  let scope₁ := requestScope V r₁
  let scope₂ := requestScope V r₂
  scope₁.threads.contains t₂ && scope₂.threads.contains t₁

def scopeIntersection : (V : ValidScopes) → Request → Request → @Pop.Scope V
  | V, r_old, r_new => Id.run do
    let old_scope := ScopedRC.requestScope V r_old
    let new_scope := ScopedRC.requestScope V r_new
    let intersection := V.intersection old_scope new_scope
    return intersection.get!

def scopesMatch : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
    let scope := scopeIntersection V r_old r_new |>.threads
    scope.contains r_old.thread && scope.contains r_new.thread

-- Some shortcuts
def isAcq (req : Request) : Bool :=
  req.basic_type.type.sem == ScopedRC.Semantics.acq

def isRel (req : Request) : Bool :=
  req.basic_type.type.sem == ScopedRC.Semantics.rel

/-
any -> rel ; acq -> any ; r -> w
-/
def order : ValidScopes → Request → Request → Bool
  | V, r_old, r_new =>
  let readtowrite := (r_old.thread == r_new.thread) && (r_old.isRead && r_new.isWrite)
  let reltoacq := (r_old.thread == r_new.thread) && (isRel r_old) && (isAcq r_new)
  let acqtoany := (r_old.thread == r_new.thread) && (isAcq r_old)
  let pred := r_old.isPredecessorAt r_new.thread && (isRel r_new)
  let newrel := (isRel r_new) && (r_new.thread == r_old.thread || r_old.isPredecessorAt r_new.thread)
  let samemem_reads := r_old.address? == r_new.address? && r_old.isRead && r_new.isRead
  scopesMatch V r_old r_new &&
  (readtowrite || acqtoany || newrel || reltoacq || pred || samemem_reads)

def blockingSemantics : Request → BlockingSemantics
    | req => reqBlockingSemantics req.basic_type.type

 def predecessorConstraints : SystemState → RequestId → RequestId → Bool
   | state, writeId, readId =>
       match (state.requests.getReq? writeId), (state.requests.getReq? readId) with
         | some write, some read => scopeInclusive state.scopes write read
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
        | "cta" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          panic! s!"(read) invalid ScopedRC scope: {scopeStr}"
      let sem := match semStr with
        | "acq" => Semantics.acq
        | "rlx" => Semantics.rlx
        | _ =>
          panic! s!"(read) invalid ScopedRC semantics: {semStr}"
      BasicRequest.read rr
      {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed ScopedRC read request: W.{scope_sem}"

def mkWrite (scope_sem : String) (addr : Address) (val : Value) (_ : String) : BasicRequest :=
  let wr : WriteRequest := match val with
    | some v => { addr := addr, val := .const v, atomicity := .nonatomic}
    | none => { addr := addr, val := .failed, atomicity := .nonatomic}
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.write wr
              {scope := Scope.sys, sem := Semantics.rlx}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          panic! s!"(write) invalid ScopedRC scope: {scopeStr}"
      let sem := match semStr with
        | "rel" => Semantics.rel
        | "rlx" => Semantics.rlx
        | _ =>
          panic! s!"(write) invalid ScopedRC semantics: {semStr}"
      BasicRequest.write wr {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed ScopedRC read request: W.{scope_sem}"

def mkFence (scope_sem : String) (_ : String) : BasicRequest :=
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.fence
              {scope := Scope.sys, sem := Semantics.rlx}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "gpu" => Scope.gpu
        | "sys" => Scope.sys
        | _ =>
          panic! s!"(fence) invalid ScopedRC scope: {scopeStr}"
      let sem := match semStr with
        | "rel" => Semantics.rel
        | "acq" => Semantics.acq
        | "rlx" => Semantics.rlx
        | _ =>
          panic! s!"(fence) invalid ScopedRC semantics: {semStr}"
      BasicRequest.fence {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed ScopedRC read request: Fence.{scope_sem}"

def mkRMW (_ : String) (addr: Address) (_ : String) : BasicRequest × BasicRequest :=
  dbg_trace "unipmelmented RMWs in ScopedRC"
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

end Litmus
