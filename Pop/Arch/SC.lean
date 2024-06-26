-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.States
import Pop.Litmus
import Pop.Util

open Pop Util

namespace SC
inductive Req
  | mk : Req
  deriving BEq, Inhabited

instance : ToString Req where toString := λ _ => ""

instance : ArchReq where
  type := SC.Req
  instBEq := SC.instBEqReq
  instInhabited := SC.instInhabitedReq
  instToString := SC.instToStringReq

def blockingSemantics (req : Request) : BlockingSemantics :=
  if req.isMem then
    [ .Read2ReadPred, .Read2WritePred, .Write2Write, .Write2Read]
  else if req.isFence then --
    panic! "No fences in SC"
  else -- dependency (for now handled by "thread subsystem")
    [ ]

-- Order everything in a thread
def order : ValidScopes → Request → Request → Bool
  | _, r₁, r₂ => r₁.thread == r₂.thread

instance : Arch where
  req := instArchReq
  orderCondition :=  SC.order
  blockingSemantics := blockingSemantics

namespace Litmus

def mkRead (_ : String ) (addr : Address) (_ : String) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none, atomicity := .nonatomic}
  BasicRequest.read rr default

def mkWrite (_ : String) (addr : Address) (val : Value) (_ : String) : BasicRequest :=
  let wr : WriteRequest := match val with
    | some v => { addr := addr, val := .const v, atomicity := .nonatomic}
    | none => { addr := addr, val := .failed, atomicity := .nonatomic}
  BasicRequest.write wr default

def mkFence (_ : String) (_ : String) : BasicRequest := panic! "SC should not have fences"

def mkRMW (_ : String) (addr: Address) (_ : String) : BasicRequest × BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := .fetchAndAdd, atomicity := .transactional}
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none, atomicity := .transactional}
  (BasicRequest.read rr default, BasicRequest.write wr default)

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkRMW := mkRMW
  mkFence := mkFence

end Litmus

end SC
