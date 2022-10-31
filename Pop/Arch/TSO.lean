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

def order : ValidScopes → Request → Request → Bool
  | _, r₁, r₂ =>
    let fences := (r₁.isFence || r₂.isFence)
    let sc_per_loc := r₁.address? == r₂.address?
    let ppo := (r₁.thread == r₂.thread) && !(r₁.isWrite && r₂.isRead)
    fences || sc_per_loc || ppo

def propagate : SystemState → RequestId → ThreadId → Bool
  | st, reqId, _ =>
    let sscope := st.scopes.systemScope
    let pred := st.orderPredecessors sscope reqId
    st.idsToReqs pred |>.all λ req => req.fullyPropagated sscope

instance : Arch where
  req := instArchReq
  propagateConstraints := x86.propagate
  orderCondition :=  x86.order

def toAlloy : String → BasicRequest → String
    | moduleName, .read _ _ => moduleName ++ "/Read"
    | moduleName, .write _ _ => moduleName ++ "/Write"
    | moduleName, .fence _ => moduleName ++ "/Fence"
def alloyName := "tso"

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
  alloyName := alloyName
  toAlloy := toAlloy

end Litmus

end x86
