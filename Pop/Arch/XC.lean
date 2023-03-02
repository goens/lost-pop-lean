-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.States
import Pop.Litmus
import Pop.Util

open Pop Util

namespace XC

inductive Scope
  | cta
  | sys
  deriving Inhabited, BEq, Repr

def Scope.intersection : Scope → Scope → Scope
  | .cta, _ => cta
  | .sys, s => s

infixl:85 "∩" => Scope.intersection

inductive Semantics
  | sc
  | rel
  | acq
  | rlx
  | dep
  deriving Inhabited, BEq, Repr

structure Req where
  (scope : Scope)
  (sem : Semantics)
  deriving BEq

instance : Inhabited Req where default :=
  { scope := Scope.sys, sem := Semantics.sc}

def Scope.toString : Scope → String
  | .cta => "cta"
  | .sys => "sys"

def Semantics.toString : Semantics → String
  | .sc => "sc"
  | .rel => "rel"
  | .acq => "acq"
  | .dep => "dep"
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
    | .acq => [.Read2ReadNoPred, .Read2WriteNoPred]
    | .sc => [.Read2WritePred, .Write2Write, .Read2ReadPred, .Write2Read]
    | .dep => [.Read2ReadNoPred, .Read2WriteNoPred]

instance : ArchReq where
  type := XC.Req
  instBEq := XC.instBEqReq
  instInhabited := XC.instInhabitedReq
  isPermanentRead := λ _ => false
  instToString := XC.instToStringReq

def getThreadScope (valid : ValidScopes) (thread : ThreadId) (scope : Scope) :=
  let containing := valid.containThread thread
  -- TODO: Could I get rid of this sorting (from the ListTree structure)?
    |>.toArray |>.qsort (λ l₁ l₂ => l₁.threads.length < l₂.threads.length)
  match scope with
  | .sys => valid.systemScope
  | .cta => if let some cta := containing[0]?
    then cta
    else panic! "invalid cta scope"

def requestScope (valid : ValidScopes) (req : Request) : @Pop.Scope valid :=
  getThreadScope valid req.thread req.basic_type.type.scope

def scopeInclusive (V : ValidScopes) (r₁ r₂ : Request) : Bool :=
  let (t₁,t₂) := (r₁.thread, r₂.thread)
  let scope₁ := requestScope V r₁
  let scope₂ := requestScope V r₂
  scope₁.threads.contains t₂ && scope₂.threads.contains t₁

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
    let old_scope := XC.requestScope V r_old
    let new_scope := XC.requestScope V r_new
    let intersection := V.intersection old_scope new_scope
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
  let readtowrite := (r_old.thread == r_new.thread) && (r_old.isRead && r_new.isWrite)
  let fences := r_old.isFence || r_new.isFence
  scopesMatch V r_old r_new && (readtowrite || fences)

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
        | "cta" => Scope.cta
        | "sys" => Scope.sys
        | _ =>
          panic! s!"(read) invalid XC scope: {scopeStr}"
      let sem := match semStr with
        | "acq" => Semantics.acq
        | "rlx" => Semantics.rlx
        | _ =>
          panic! s!"(read) invalid XC semantics: {semStr}"
      BasicRequest.read rr
      {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed XC read request: W.{scope_sem}"

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
        | "sys" => Scope.sys
        | _ =>
          panic! s!"(write) invalid XC scope: {scopeStr}"
      let sem := match semStr with
        | "rel" => Semantics.rel
        | "rlx" => Semantics.rlx
        | _ =>
          panic! s!"(write) invalid XC semantics: {semStr}"
      BasicRequest.write wr {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed XC read request: W.{scope_sem}"

def mkFence (scope_sem : String) (_ : String) : BasicRequest :=
  match scope_sem.splitOn "_" with
    | [""] => BasicRequest.fence
              {scope := Scope.sys, sem := Semantics.sc}
    | [scopeStr, semStr] =>
      let scope := match scopeStr with
        | "cta" => Scope.cta
        | "sys" => Scope.sys
        | _ =>
          panic! s!"(fence) invalid XC scope: {scopeStr}"
      let sem := match semStr with
        | "sc" => Semantics.sc
        | "rel" => Semantics.rel
        | "acq" => Semantics.acq
        | "dep" => Semantics.dep
        | _ =>
          panic! s!"(fence) invalid XC semantics: {semStr}"
      BasicRequest.fence {scope := scope, sem := sem}
    | _ =>
      panic! s!"malformed XC read request: Fence.{scope_sem}"

def mkRMW (_ : String) (addr: Address) (_ : String) : BasicRequest × BasicRequest :=
  dbg_trace "unipmelmented RMWs in XC"
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
