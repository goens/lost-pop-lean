import Pop.States
import Pop.Litmus
import Pop.Program
import Pop.Util

open Pop Util

namespace x86
inductive Req
  | mk : Req
  deriving BEq, Inhabited

instance : ToString Req where toString := λ _ => ""

instance : ArchReq where
  type := x86.Req
  instBEq := x86.instBEqReq
  instInhabited := x86.instInhabitedReq
  instToString := x86.instToStringReq
  isPermanentRead := λ _ => true

def reorder : Request → Request → Bool
  | r₁, r₂ => if r₁.isBarrier || r₂.isBarrier
  then false
  else
  let sc_per_loc := r₁.address? != r₂.address?
  --dbg_trace s!"sc_per_loc: {sc_per_loc}"
  let ppo := (r₁.thread != r₂.thread) || !(r₂.isWrite && r₁.isRead)
  --dbg_trace s!"ppo: {sc_per_loc}"
  if sc_per_loc then ppo else false
  -- TODO: satisfied but not deleted?

def propagate : SystemState → RequestId → ThreadId → Bool
  | st, reqId, _ =>
    let sscope := st.scopes.systemScope
    let pred := st.orderPredecessors sscope reqId
    st.idsToReqs pred |>.all λ req => req.fullyPropagated sscope

def requestScope (valid : ValidScopes) (_ : Request) : @Scope valid :=
  valid.systemScope

instance : Arch where
  req := instArchReq
  acceptConstraints := λ _ _ _ => true
  propagateConstraints := x86.propagate
  satisfyReadConstraints := λ _ _ _ => true
  reorderCondition :=  x86.reorder
  requestScope := x86.requestScope

namespace Litmus

def mkRead (_ : String ) (addr : Address) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  BasicRequest.read rr default

def mkWrite (_ : String) (addr : Address) (val : Value) : BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := val}
  BasicRequest.write wr default

def mkBarrier (_ : String) : BasicRequest := BasicRequest.barrier default

def mkInitState (n : Nat) :=
  let valid_scopes : ValidScopes :=
    { system_scope := List.range n, scopes := ListTree.leaf (List.range n)}
  SystemState.init valid_scopes


instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkBarrier := mkBarrier
  mkInitState := mkInitState

def IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
def IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
def MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
def MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |}
def MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |}
def MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|}
def N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |}
def dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |}
def dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |}
--def causality := {| W x = 1 || R x; Fence; W x = 2 || R x; W|}

def x86_2 := [MP,MP_fence1,MP_fence2,MP_fence, N7, dekkers, dekkers_fence]
def x86_4 := [IRIW, IRIW_fences]

def allTso : List Litmus.Test := x86_2 ++ x86_4

end Litmus

end x86
