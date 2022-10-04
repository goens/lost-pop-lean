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

def reorder : ValidScopes → Request → Request → Bool
  | _, r_old, r_new =>
  let relacq₁ := (r_old.isReadAcq && r_new.isWriteRel) b⇒ (r_old.address? != r_new.address?)
  let relacq₂ := !r_new.isWriteRel
  let relacq₃ := r_old.isReadAcq b⇒ (r_new.thread != r_old.thread)
  let relacq₄ := (r_new.isReadAcq && r_old.isWriteRel) b⇒ (r_new.thread != r_old.thread)
  let orig₁ := !r_new.isBarrier && !r_old.isBarrier
  let orig₂ := (r_new.isMem && r_old.isMem && !r_new.isSatisfied && !r_old.isSatisfied)
                b⇒ (r_new.address? != r_old.address?)
  relacq₁ && relacq₂ && relacq₃ && relacq₄ && orig₁ && orig₂

def satisfyRead (state : SystemState) (r_read_addr : RequestId) (r_write_addr : RequestId)
  : Bool :=
  match state.requests.getReq? r_read_addr, state.requests.getReq? r_write_addr with
  | some r_read, some r_write => (r_read.isReadAcq && r_write.isWriteRel)
    b⇒ r_write.fullyPropagated state.scopes.systemScope
  | _, _ => panic! s!"invalid read request ({r_read_addr}) and/or write request ({r_write_addr})"

instance : Arch where
  req := instArchReq
  reorderCondition :=  reorder

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

def mkBarrier (reqtype : String) (_ : String): BasicRequest :=
  match reqtype with
    | "" => BasicRequest.barrier Req.other
    | _ => panic! "invalid barrier type: {reqtype}"

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkBarrier := mkBarrier

deflitmus WRC := {| W x=1 || R. acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|}
deflitmus WRC_two_deps := {| W x=1 || R. acq x // 1;dep W y = 1 || R y // 1 ;dep R x // 0|}
deflitmus WRC_rel := {| W. rel x=1 || R. acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|}
deflitmus WRC_acq := {| W x=1 || R. acq x // 1; W y = 1 || R. acq y // 1 ;dep R x // 0|}
deflitmus WRC_no_dep := {| W x=1 || R. acq x // 1; W y = 1 || R y // 1 ; R x // 0|}
deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
deflitmus IRIW_3_threads := {| W x=1; W y=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 |}
deflitmus IRIW_acq := {| W x=1 ||  R. acq x // 1;  R. acq y // 0 || R. acq  y // 1; R. acq x // 0 || W y=1 |}
deflitmus IRIW_first_acq := {| W x=1 ||  R. acq x // 1;  R y // 0 || R. acq  y // 1; R x // 0 || W y=1 |}
deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
deflitmus MP_rel := {| W. rel x=1; W. rel y=1 ||  R y // 1; R x // 0 |}
deflitmus MP_acq := {| W x=1; W y=1 ||  R. acq y //1; R. acq x // 0 |}
deflitmus MP_relacq := {| W. rel x=1; W. rel y=1 ||  R. acq y //1; R. acq x // 0 |}
deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |}
deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |}
deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |}
--def causality := {| W x = 1 || R x; Fence; W x = 2 || R x; W|}

def allARM := litmusTests!
def arm_2 := allARM.filter λ lit => lit.numThreads == 2
def arm_3 := allARM.filter λ lit => lit.numThreads == 3
def arm_4 := allARM.filter λ lit => lit.numThreads == 4

end Litmus
