-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

-- TODO: This is a lot of code duplication from the other compound model.
-- We should be able to make it architecture polymorphic
-- (Or just get rid of the arch typeclass and let architectures be syntactic sugar somehow? Not clear if this would work with the order constraints and arch-specific meet)
import Pop.States
import Pop.Litmus
import Pop.Util
import Pop.Arch.TSO
import Pop.Arch.XC

open Pop Util

namespace CompoundXCTSO

abbrev Req := x86.Req ⊕ XC.Req
instance : BEq Req where beq := λ r r' => match r, r' with
  | .inl r, .inl r' => BEq.beq r r'
  | .inr r, .inr r' => BEq.beq r r'
  | _, _ => false

def Req.toString : Req → String
  | .inl r => s!"{r}"
  | .inr r => s!"{r}"

instance : ToString Req where toString := Req.toString
instance : Inhabited Req where default := .inl default

instance : ArchReq where
  type := Req
  instBEq := instBEqReq
  instInhabited := instInhabitedReq
  instToString := instToStringReq
  isPermanentRead := λ _ => false

def x86ReqToCompoundXCTSO : @BasicRequest x86.instArchReq → @BasicRequest CompoundXCTSO.instArchReq
  -- this won't go through pattern match, no idea how to get it to work
  -- | .read rr ty => .read rr (.inl ty)
  | req => if @BasicRequest.isRead x86.instArchReq req
              then .read (@BasicRequest.readRequest? x86.instArchReq req).get! (.inl $ @BasicRequest.type x86.instArchReq req)
           else if @BasicRequest.isWrite x86.instArchReq req
              then .write (@BasicRequest.writeRequest? x86.instArchReq req).get! (.inl $ @BasicRequest.type x86.instArchReq req)
           else .fence (.inl $ @BasicRequest.type x86.instArchReq req)

instance : Coe (@BasicRequest x86.instArchReq) (@BasicRequest CompoundXCTSO.instArchReq) where coe := x86ReqToCompoundXCTSO

def xcReqToCompoundXCTSO : @BasicRequest XC.instArchReq → @BasicRequest CompoundXCTSO.instArchReq
  | req => if @BasicRequest.isRead XC.instArchReq req
              then .read (@BasicRequest.readRequest? XC.instArchReq req).get! (.inr $ @BasicRequest.type XC.instArchReq req)
           else if @BasicRequest.isWrite XC.instArchReq req
              then .write (@BasicRequest.writeRequest? XC.instArchReq req).get! (.inr $ @BasicRequest.type XC.instArchReq req)
           else .fence (.inr $ @BasicRequest.type XC.instArchReq req)

instance : Coe (@BasicRequest XC.instArchReq) (@BasicRequest CompoundXCTSO.instArchReq) where coe := xcReqToCompoundXCTSO

def compoundReqToXC : @BasicRequest CompoundXCTSO.instArchReq → Option (@BasicRequest XC.instArchReq)
  | .read rr (.inr xcreq) => some $ @BasicRequest.read XC.instArchReq rr xcreq
  | .write wr (.inr xcreq) => some $ @BasicRequest.write XC.instArchReq wr xcreq
  | .fence (.inr xcreq) => some $ @BasicRequest.fence XC.instArchReq xcreq
  | _ => none

def compoundReqToTSO : @BasicRequest CompoundXCTSO.instArchReq → Option (@BasicRequest x86.instArchReq)
  | .read rr (.inl x86req) => some $ @BasicRequest.read x86.instArchReq rr x86req
  | .write wr (.inl x86req) => some $ @BasicRequest.write x86.instArchReq wr x86req
  | .fence (.inl x86req) => some $ @BasicRequest.fence x86.instArchReq x86req
  | _ => none


def compoundTSOReqToCompoundXCTSOXC : @BasicRequest CompoundXCTSO.instArchReq → @BasicRequest CompoundXCTSO.instArchReq
  | .read rr (.inl _) => .read rr (.inr { scope := XC.Scope.sys, sem := .rlx})
  | .write wr (.inl _) => .write wr (.inr { scope := XC.Scope.sys, sem := .rlx})
  | .fence (.inl _) => .fence (.inr { scope := XC.Scope.sys, sem := .sc})
  | req => req

-- TODO: maybe make these two into a single function : @Request CompoundXCTSO.instArchReq) → (@Request XC.instArchReq) ⊕ (@Request x86.instArchReq)
def _root_.Pop.Request.toXC? (req : @Request CompoundXCTSO.instArchReq) : Option (@Request XC.instArchReq) :=
  match compoundReqToXC req.basic_type with
    | none => none
    | some bt => @Request.mk XC.instArchReq req.id req.propagated_to req.predecessor_at req.thread bt req.occurrence req.pairedRequest?

def _root_.Pop.Request.toTSO'? (req : @Request CompoundXCTSO.instArchReq) : Option (@Request x86.instArchReq) :=
  match compoundReqToTSO req.basic_type with
    | none => none
    | some bt => @Request.mk x86.instArchReq req.id req.propagated_to req.predecessor_at req.thread bt req.occurrence none


def _root_.Pop.Request.toXC!? (req : @Request CompoundXCTSO.instArchReq) : Option (@Request XC.instArchReq) :=
  match compoundReqToXC (compoundTSOReqToCompoundXCTSOXC req.basic_type) with
    | none => none
    | some bt => @Request.mk XC.instArchReq req.id req.propagated_to req.predecessor_at req.thread bt req.occurrence req.pairedRequest?

def order : ValidScopes → Request → Request → Bool
  | V, r₁, r₂ => match r₁.toTSO'?, r₂.toTSO'? with
    | some x86r₁, some x86r₂ => x86.order V x86r₁ x86r₂
    | _, _ => match r₁.toXC!?, r₂.toXC!? with
        | some xcr₁, some xcr₂ => XC.order V xcr₁ xcr₂
        | _, _ => false

def scopeIntersection : (valid : ValidScopes) → Request → Request → @Scope valid
  | valid, r₁, r₂ =>
    match r₁.toXC!?, r₂.toXC!? with
      | some r₁xc, some r₂xc => XC.scopeIntersection valid r₁xc r₂xc
      | some r₁xc, none => XC.requestScope valid r₁xc
      | none      , some r₂xc => XC.requestScope valid r₂xc
      | none      , none => valid.systemScope

def blockingSemantics (req : Request) : BlockingSemantics :=
    match req.toXC? with
        | some xcreq => XC.blockingSemantics xcreq
        | none => match req.toTSO'? with
             | some tsoreq => x86.blockingSemantics tsoreq
             | none => unreachable!

 def predecessorConstraints : SystemState → RequestId → RequestId → Bool
   | state, writeId, readId =>
       match (state.requests.getReq? writeId), (state.requests.getReq? readId) with
         | some write, some read => match write.toXC!?, read.toXC!? with
             | some xcwrite, some xcread => XC.scopesMatch state.scopes xcwrite xcread
             | _, _ => false
         | _, _ => false

instance : Arch where
  req := instArchReq
  orderCondition := order
  scopeIntersection := scopeIntersection
  blockingSemantics := blockingSemantics
  predecessorConstraints := predecessorConstraints

namespace Litmus
def mkRead (typedescr : String ) (addr : Address) (threadType : String): BasicRequest :=
  match threadType with
    | "XC" => XC.Litmus.mkRead typedescr addr ""
    | "x86" => x86.Litmus.mkRead typedescr addr ""
    | t => panic! s!"Unknown Thread type: {t}"

def mkWrite (typedescr : String) (addr : Address) (val : Value) (threadType : String): BasicRequest :=
  match threadType with
    | "XC" => XC.Litmus.mkWrite typedescr addr val ""
    | "x86" => x86.Litmus.mkWrite typedescr addr val ""
    | t => panic! s!"Unknown Thread type: {t}"

def mkRMW (_ : String) (_ : Address) (_ : String) : BasicRequest × BasicRequest :=
  panic! "RMW unimplemented in CompoundXCTSO"

def mkFence (typedescr : String) (threadType : String) : BasicRequest :=
  match threadType with
    | "XC" => XC.Litmus.mkFence typedescr ""
    | "x86" => x86.Litmus.mkFence typedescr ""
    | t => panic! s!"Unknown Thread type: {t}"


instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkRMW := mkRMW
  mkFence := mkFence

end Litmus

def importTSOTransition : @Transition x86.instArch → @Transition CompoundXCTSO.instArch
  | @Transition.acceptRequest x86.instArch br th => .acceptRequest (x86ReqToCompoundXCTSO br) th
  | @Transition.propagateToThread x86.instArch rid thid => .propagateToThread rid thid
  | @Transition.satisfyRead x86.instArch rd wr => .satisfyRead rd wr
  | @Transition.dependency x86.instArch dep => .dependency dep

def importTSOSystemInit : @SystemState x86.instArchReq → @SystemState CompoundXCTSO.instArchReq
  | state =>
    let scopes := @SystemState.scopes x86.instArchReq state
    let threadTypes := λ _ => "x86"
    SystemState.init scopes threadTypes

def importTSOLitmus : @Litmus.Test x86.instArch → @Litmus.Test CompoundXCTSO.instArch
  | test =>
  { axiomaticAllowed := @Litmus.Test.axiomaticAllowed x86.instArch test,
    name := "x86_" ++ @Litmus.Test.name x86.instArch test,
    expected := (@Litmus.Test.expected x86.instArch test),
    program := (@Litmus.Test.program x86.instArch test).map λ th => th.map importTSOTransition,
    guideTraces := (@Litmus.Test.guideTraces x86.instArch test).map λ tr => tr.map importTSOTransition
    initTransitions := (@Litmus.Test.initTransitions x86.instArch test).map importTSOTransition
    initState := importTSOSystemInit (@Litmus.Test.initState x86.instArch test),
    description := (@Litmus.Test.description x86.instArch test),
    : Litmus.Test}

def importXCTransition : @Transition XC.instArch → @Transition CompoundXCTSO.instArch
  | @Transition.acceptRequest XC.instArch br th => .acceptRequest (xcReqToCompoundXCTSO br) th
  | @Transition.propagateToThread XC.instArch rid thid => .propagateToThread rid thid
  | @Transition.satisfyRead XC.instArch rd wr => .satisfyRead rd wr
  | @Transition.dependency XC.instArch dep => .dependency dep

def importXCSystemInit : @SystemState XC.instArchReq → @SystemState CompoundXCTSO.instArchReq
  | state =>
    let scopes := @SystemState.scopes XC.instArchReq state
    let threadTypes := λ _ => "XC"
    SystemState.init scopes threadTypes

def importXCLitmus : @Litmus.Test XC.instArch → @Litmus.Test CompoundXCTSO.instArch
  | test =>
  { axiomaticAllowed := @Litmus.Test.axiomaticAllowed XC.instArch test,
    name := "XC_" ++ @Litmus.Test.name XC.instArch test,
    expected := (@Litmus.Test.expected XC.instArch test),
    program := (@Litmus.Test.program XC.instArch test).map λ th => th.map importXCTransition,
    guideTraces := (@Litmus.Test.guideTraces XC.instArch test).map λ tr => tr.map importXCTransition
    initTransitions := (@Litmus.Test.initTransitions XC.instArch test).map importXCTransition
    initState := importXCSystemInit (@Litmus.Test.initState XC.instArch test)
    description := (@Litmus.Test.description XC.instArch test),
    : Litmus.Test}

end CompoundXCTSO
