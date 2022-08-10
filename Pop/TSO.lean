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

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkBarrier := mkBarrier

def IRIW := {| W x=1 ||  R x; R y || R y; R x || W y=1 |}
def IRIW_fences := {| W x=1 ||  R x; Fence; R y || R y; Fence; R x || W y=1 |}
def MP := {|  W x=1; W y=1 ||  R y; R x |}
def MP_fence1 := {| W x=1; Fence; W y=1 ||  R y; R x |}
def MP_fence2 := {| W x=1; W y=1 ||  R y; Fence; R x |}
def MP_fence := {| W x=1; Fence; W y=1 ||  R y; Fence; R x |}
def N7 := {| W x=1; R x; R y || W y=1; R y; R x |}

def x86_2_inst := [MP,MP_fence1,MP_fence2,MP_fence, N7]
def x86_4_inst := [IRIW, IRIW_fences]

def valid_scopes_2 : ValidScopes := { system_scope := List.range 2, scopes := ListTree.leaf (List.range 2)}
def valid_scopes_4 : ValidScopes := { system_scope := List.range 4, scopes := ListTree.leaf (List.range 4)}

def inittso_2 : SystemState := SystemState.init valid_scopes_2
def inittso_4 : SystemState := SystemState.init valid_scopes_4

def x86_2 := x86_2_inst.zip (List.replicate x86_2_inst.length inittso_2)
def x86_4 := x86_4_inst.zip (List.replicate x86_4_inst.length inittso_4)
def allTso := x86_2 ++ x86_4

end Litmus
