import Pop.States
import Pop.Litmus
import Pop.Util

open Pop Util

namespace ARM

inductive Req
  | rel
  | acq
  | other
  deriving Inhabited, BEq

def Req.toString : Req → String
  | .rel => "rel "
  | .acq => "acq "
  | .other => ""

instance : ToString Req where toString := Req.toString

def Req.isPermanentRead : Req → Bool
  | .rel => true
  | .acq => true
  | _ => false

instance : ArchReq where
  type := Req
  instBEq := instBEqReq
  instInhabited := instInhabitedReq
  isPermanentRead := Req.isPermanentRead
  instToString := instToStringReq

private def _root_.Pop.Request.isReadAcq : Request → Bool :=
 λ r => r.isRead && r.basic_type.type == ARM.Req.acq

private def _root_.Pop.Request.isWriteRel : Request → Bool :=
 λ r => r.isWrite && r.basic_type.type == ARM.Req.rel

infixl:85 "b⇒" => λ a b => !a || b

def order : ValidScopes → Request → Request → Bool
  | _, r_old, r_new =>
  let relacq₁ := (r_old.isReadAcq && r_new.isWriteRel) && (r_old.address? == r_new.address?)
  let relacq₂ := r_new.isWriteRel
  let relacq₃ := r_old.isReadAcq && (r_new.thread == r_old.thread)
  let relacq₄ := (r_new.isReadAcq && r_old.isWriteRel) && (r_new.thread == r_old.thread)
  let orig₁ := r_new.isFence || r_old.isFence
  let orig₂ := (r_new.isMem && r_old.isMem && !r_new.isSatisfied && !r_old.isSatisfied)
                && (r_new.address? == r_old.address?)
  (relacq₁ || relacq₂ || relacq₃ || relacq₄ || orig₁ || orig₂)

def satisfyRead (state : SystemState) (r_read_addr : RequestId) (r_write_addr : RequestId)
  : Bool :=
  match state.requests.getReq? r_read_addr, state.requests.getReq? r_write_addr with
  | some r_read, some r_write => (r_read.isReadAcq && r_write.isWriteRel)
    b⇒ r_write.fullyPropagated state.scopes.systemScope
  | _, _ => panic! s!"invalid read request ({r_read_addr}) and/or write request ({r_write_addr})"

instance : Arch where
  req := instArchReq
  orderCondition :=  order

namespace Litmus

def mkRead (reqtype : String ) (addr : Address) (_ : String): BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  match reqtype with
    | "" => BasicRequest.read rr Req.other
    | "acq" => BasicRequest.read rr Req.acq
    | _ => panic! "invalid read request type: {reqtype}"

def mkWrite (reqtype : String) (addr : Address) (val : Value) (_ : String): BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := val}
  match reqtype with
    | "" => BasicRequest.write wr Req.other
    | "rel" => BasicRequest.write wr Req.rel
    | _ => panic! "invalid read request type: {reqtype}"

def mkFence (reqtype : String) (_ : String): BasicRequest :=
  match reqtype with
    | "" => BasicRequest.fence Req.other
    | _ => panic! "invalid fence type: {reqtype}"

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkFence := mkFence

end Litmus
