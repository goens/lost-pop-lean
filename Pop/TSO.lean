import Pop.States
import Pop.Litmus
import Pop.Program
import Pop.Util

open Pop Util

inductive DefaultReqType
  | mk : DefaultReqType
  deriving BEq, Inhabited

instance : ArchReq where
  type := DefaultReqType
  beq_inst := instBEqDefaultReqType
  inhabited_inst := instInhabitedDefaultReqType

def tso_reorder : Request → Request → Bool
  | r₁, r₂ => if r₁.isBarrier || r₂.isBarrier
  then false
  else
  let sc_per_loc := r₁.address? != r₂.address?
  --dbg_trace s!"sc_per_loc: {sc_per_loc}"
  let ppo := (r₁.thread != r₂.thread) || !(r₂.isWrite && r₁.isRead)
  --dbg_trace s!"ppo: {sc_per_loc}"
  if sc_per_loc then ppo else false
  -- TODO: satisfied but not deleted?

def tso_propagate : SystemState → RequestId → ThreadId → Bool
  | st, reqId, _ =>
    let sscope := st.scopes.systemScope
    let pred := st.orderPredecessors sscope reqId
    st.idsToReqs pred |>.all λ req => req.fullyPropagated sscope

instance : Arch where
  req := instArchReq
  acceptConstraints := λ _ _ _ => true
  propagateConstraints := tso_propagate
  satisfyReadConstraints := λ _ _ _ => true
  reorderCondition :=  tso_reorder

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

def x86_2 := [MP,MP_fence1,MP_fence2,MP_fence, N7]
def x86_4 := [IRIW, IRIW_fences]

def allTso : List Litmus.Test := x86_2 ++ x86_4

end Litmus
