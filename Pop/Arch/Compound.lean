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
  | .inl r => s!"x86[{r}]"
  | .inr r => s!"PTX[{r}]"
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

instance : Arch where
  req := instArchReq
  orderCondition := order
  scopeIntersection := scopeIntersection

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


end Compound
