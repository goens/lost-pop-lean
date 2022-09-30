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
  | _, r₁, r₂ => if r₁.isBarrier || r₂.isBarrier
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

instance : Arch where
  req := instArchReq
  propagateConstraints := x86.propagate
  reorderCondition :=  x86.reorder

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

deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
deflitmus IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
deflitmus MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |}
deflitmus MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |}
deflitmus MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|}
deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |}
deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |}
deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |}
--deflitmus causality := {| W x = 1 || R x; Fence; W x = 2 || R x; W|}

def allTSO := litmusTests!
def tso_2 := allTSO.filter λ lit => lit.numThreads == 2
def tso_3 := allTSO.filter λ lit => lit.numThreads == 3
def tso_4 := allTSO.filter λ lit => lit.numThreads == 4

end Litmus

end x86
