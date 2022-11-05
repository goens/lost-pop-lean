import Pop.States
import Pop.Litmus
import Pop.Util
import Pop.Arch.TSO
import Pop.Arch.PTX

open Pop Util

namespace Compound

abbrev Req := x86.Req ⊕ PTX.Req
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

def x86ReqToCompound : @BasicRequest x86.instArchReq → @BasicRequest Compound.instArchReq
  -- this won't go through pattern match, no idea how to get it to work
  -- | .read rr ty => .read rr (.inl ty)
  | req => if @BasicRequest.isRead x86.instArchReq req
              then .read (@BasicRequest.readRequest? x86.instArchReq req).get! (.inl $ @BasicRequest.type x86.instArchReq req)
           else if @BasicRequest.isWrite x86.instArchReq req
              then .write (@BasicRequest.writeRequest? x86.instArchReq req).get! (.inl $ @BasicRequest.type x86.instArchReq req)
           else .fence (.inl $ @BasicRequest.type x86.instArchReq req)

instance : Coe (@BasicRequest x86.instArchReq) (@BasicRequest Compound.instArchReq) where coe := x86ReqToCompound

def ptxReqToCompound : @BasicRequest PTX.instArchReq → @BasicRequest Compound.instArchReq
  | req => if @BasicRequest.isRead PTX.instArchReq req
              then .read (@BasicRequest.readRequest? PTX.instArchReq req).get! (.inr $ @BasicRequest.type PTX.instArchReq req)
           else if @BasicRequest.isWrite PTX.instArchReq req
              then .write (@BasicRequest.writeRequest? PTX.instArchReq req).get! (.inr $ @BasicRequest.type PTX.instArchReq req)
           else .fence (.inr $ @BasicRequest.type PTX.instArchReq req)

instance : Coe (@BasicRequest PTX.instArchReq) (@BasicRequest Compound.instArchReq) where coe := ptxReqToCompound

def compoundReqToPTX : @BasicRequest Compound.instArchReq → Option (@BasicRequest PTX.instArchReq)
  | .read rr (.inr ptxreq) => some $ @BasicRequest.read PTX.instArchReq rr ptxreq
  | .write wr (.inr ptxreq) => some $ @BasicRequest.write PTX.instArchReq wr ptxreq
  | .fence (.inr ptxreq) => some $ @BasicRequest.fence PTX.instArchReq ptxreq
  | _ => none

def compoundReqToTSO : @BasicRequest Compound.instArchReq → Option (@BasicRequest x86.instArchReq)
  | .read rr (.inl x86req) => some $ @BasicRequest.read x86.instArchReq rr x86req
  | .write wr (.inl x86req) => some $ @BasicRequest.write x86.instArchReq wr x86req
  | .fence (.inl x86req) => some $ @BasicRequest.fence x86.instArchReq x86req
  | _ => none

-- TODO: maybe make these two into a single function : @Request Compound.instArchReq) → (@Request PTX.instArchReq) ⊕ (@Request x86.instArchReq)
def _root_.Pop.Request.toPTX? (req : @Request Compound.instArchReq) : Option (@Request PTX.instArchReq) :=
  match compoundReqToPTX req.basic_type with
    | none => none
    | some bt => @Request.mk PTX.instArchReq req.id req.propagated_to req.predecessor_at req.thread bt req.occurrence

def _root_.Pop.Request.toTSO? (req : @Request Compound.instArchReq) : Option (@Request x86.instArchReq) :=
  match compoundReqToTSO req.basic_type with
    | none => none
    | some bt => @Request.mk x86.instArchReq req.id req.propagated_to req.predecessor_at req.thread bt req.occurrence

def order : ValidScopes → Request → Request → Bool
  | V, r₁, r₂ => match r₁.toTSO?, r₂.toTSO? with
    | some x86r₁, some x86r₂ => x86.order V x86r₁ x86r₂
    | _, _ => match r₁.toPTX?, r₂.toPTX? with
        | some ptxr₁, some ptxr₂ => PTX.order V ptxr₁ ptxr₂
        | _, _ => false

def scopeIntersection : (valid : ValidScopes) → Request → Request → @Scope valid
  | valid, r₁, r₂ =>
    match r₁.toPTX?, r₂.toPTX? with
      | some r₁ptx, some r₂ptx => PTX.scopeIntersection valid r₁ptx r₂ptx
      | some r₁ptx, none => PTX.requestScope valid r₁ptx
      | none      , some r₂ptx => PTX.requestScope valid r₂ptx
      | none      , none => valid.systemScope


def blockingSemantics (req : Request) : BlockingSemantics :=
    match req.toPTX? with
        | some ptxreq => PTX.blockingSemantics ptxreq
        | none => match req.toTSO? with
             | some tsoreq => x86.blockingSemantics tsoreq
             | none => unreachable!

instance : Arch where
  req := instArchReq
  orderCondition := order
  scopeIntersection := scopeIntersection
  blockingSemantics := blockingSemantics

namespace Litmus
def mkRead (typedescr : String ) (addr : Address) (threadType : String): BasicRequest :=
  match threadType with
    | "PTX" => PTX.Litmus.mkRead typedescr addr ""
    | "x86" => x86.Litmus.mkRead typedescr addr ""
    | t => panic! s!"Unknown Thread type: {t}"

def mkWrite (typedescr : String) (addr : Address) (val : Value) (threadType : String): BasicRequest :=
  match threadType with
    | "PTX" => PTX.Litmus.mkWrite typedescr addr val ""
    | "x86" => x86.Litmus.mkWrite typedescr addr val ""
    | t => panic! s!"Unknown Thread type: {t}"

def mkFence (typedescr : String) (threadType : String) : BasicRequest :=
  match threadType with
    | "PTX" => PTX.Litmus.mkFence typedescr ""
    | "x86" => x86.Litmus.mkFence typedescr ""
    | t => panic! s!"Unknown Thread type: {t}"

def toAlloy : String → BasicRequest → String
    | moduleName, br@(.read _ ty) => match ty with
      | .inl _ => moduleName ++ "/x86Read"
      | .inr _ => PTX.toAlloy moduleName (compoundReqToPTX br).get!
    | moduleName, br@(.write _ ty) => match ty with
      | .inl _ => moduleName ++ "/x86Write"
      | .inr _ => PTX.toAlloy moduleName (compoundReqToPTX br).get!
    | moduleName, br@(.fence ty) => match ty with
      | .inl _ => moduleName ++ "/mFence"
      | .inr _ => PTX.toAlloy moduleName (compoundReqToPTX br).get!
def alloyName := "cmm"

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkFence := mkFence
  alloyName := alloyName
  toAlloy := toAlloy

end Litmus

def importTSOTransition : @Transition x86.instArch → @Transition Compound.instArch
  | @Transition.acceptRequest x86.instArch br th => .acceptRequest (x86ReqToCompound br) th
  | @Transition.propagateToThread x86.instArch rid thid => .propagateToThread rid thid
  | @Transition.satisfyRead x86.instArch rd wr => .satisfyRead rd wr
  | @Transition.dependency x86.instArch dep => .dependency dep

def importTSOSystemInit : @SystemState x86.instArchReq → @SystemState Compound.instArchReq
  | state =>
    let scopes := @SystemState.scopes x86.instArchReq state
    let threadTypes := λ _ => "x86"
    SystemState.init scopes threadTypes

def importTSOLitmus : @Litmus.Test x86.instArch → @Litmus.Test Compound.instArch
  | test =>
  { axiomaticAllowed := @Litmus.Test.axiomaticAllowed x86.instArch test,
    name := "x86_" ++ @Litmus.Test.name x86.instArch test,
    expected := (@Litmus.Test.expected x86.instArch test),
    program := (@Litmus.Test.program x86.instArch test).map λ th => th.map importTSOTransition,
    guideTraces := (@Litmus.Test.guideTraces x86.instArch test).map λ tr => tr.map importTSOTransition
    initTransitions := (@Litmus.Test.initTransitions x86.instArch test).map importTSOTransition
    initState := importTSOSystemInit (@Litmus.Test.initState x86.instArch test)
    : Litmus.Test}

def importPTXTransition : @Transition PTX.instArch → @Transition Compound.instArch
  | @Transition.acceptRequest PTX.instArch br th => .acceptRequest (ptxReqToCompound br) th
  | @Transition.propagateToThread PTX.instArch rid thid => .propagateToThread rid thid
  | @Transition.satisfyRead PTX.instArch rd wr => .satisfyRead rd wr
  | @Transition.dependency PTX.instArch dep => .dependency dep

def importPTXSystemInit : @SystemState PTX.instArchReq → @SystemState Compound.instArchReq
  | state =>
    let scopes := @SystemState.scopes PTX.instArchReq state
    let threadTypes := λ _ => "PTX"
    SystemState.init scopes threadTypes

def importPTXLitmus : @Litmus.Test PTX.instArch → @Litmus.Test Compound.instArch
  | test =>
  { axiomaticAllowed := @Litmus.Test.axiomaticAllowed PTX.instArch test,
    name := "PTX_" ++ @Litmus.Test.name PTX.instArch test,
    expected := (@Litmus.Test.expected PTX.instArch test),
    program := (@Litmus.Test.program PTX.instArch test).map λ th => th.map importPTXTransition,
    guideTraces := (@Litmus.Test.guideTraces PTX.instArch test).map λ tr => tr.map importPTXTransition
    initTransitions := (@Litmus.Test.initTransitions PTX.instArch test).map importPTXTransition
    initState := importPTXSystemInit (@Litmus.Test.initState PTX.instArch test)
    : Litmus.Test}


end Compound
