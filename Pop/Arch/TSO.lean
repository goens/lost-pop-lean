import Pop.States
import Pop.Litmus
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
  isPermanentRead := λ _ => false

def reorder : ValidScopes → Request → Request → Bool
  | _, r₁, r₂ => if r₁.isFence || r₂.isFence
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
    dbg_trace "X86 propagate constraint: all {pred} fully propagated? {st.idsToReqs pred |>.all λ req => req.fullyPropagated sscope}"
    st.idsToReqs pred |>.all λ req => req.fullyPropagated sscope

instance : Arch where
  req := instArchReq
  propagateConstraints := x86.propagate
  reorderCondition :=  x86.reorder

namespace Litmus

def mkRead (_ : String ) (addr : Address) (_ : String) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  BasicRequest.read rr default

def mkWrite (_ : String) (addr : Address) (val : Value) (_ : String) : BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := val}
  BasicRequest.write wr default

def mkFence (_ : String) (_ : String) : BasicRequest := BasicRequest.fence default

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkFence := mkFence

end Litmus

end x86
