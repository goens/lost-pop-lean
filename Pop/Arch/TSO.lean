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

def blockingSemantics (req : Request) : BlockingSemantics :=
  if req.isMem then
    [ .Read2ReadPred, .Read2WritePred, .Write2Write]
  else if req.isFence then --
    [ .Read2ReadPred, .Read2WritePred, .Write2Write, .Write2Read]
  else -- dependency (for now handled by "thread subsystem")
    [ ]

def order : ValidScopes → Request → Request → Bool
  | _, r₁, r₂ => (r₁.thread == r₂.thread) && !(r₁.isWrite && r₂.isRead)

instance : Arch where
  req := instArchReq
  orderCondition :=  x86.order
  blockingSemantics := blockingSemantics

def toAlloy : String → BasicRequest → String
    | moduleName, .read _ _ => moduleName ++ "/Read"
    | moduleName, .write _ _ => moduleName ++ "/Write"
    | moduleName, .fence _ => moduleName ++ "/Fence"
def alloyName := "tso"

namespace Litmus

def mkRead (_ : String ) (addr : Address) (_ : String) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none, atomic := false}
  BasicRequest.read rr default

def mkWrite (_ : String) (addr : Address) (val : Value) (_ : String) : BasicRequest :=
  let wr : WriteRequest := match val with
    | some v => { addr := addr, val := .const v, atomic := false}
    | none => { addr := addr, val := .failed, atomic := false}
  BasicRequest.write wr default

def mkFence (_ : String) (_ : String) : BasicRequest := BasicRequest.fence default

def mkRMW (_ : String) (addr: Address) (_ : String) : BasicRequest × BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := .fetchAndAdd, atomic := true}
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none, atomic := true}
  (BasicRequest.read rr default, BasicRequest.write wr default)

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkRMW := mkRMW
  mkFence := mkFence
  alloyName := alloyName
  toAlloy := toAlloy

end Litmus

end x86
