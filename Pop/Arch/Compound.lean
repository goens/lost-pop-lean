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

def order : ValidScopes → Request → Request → Bool
/-
  -- This won't typecheck, the types *force* us to define embeddings
  | V, r₁, r₂ => match r₂.basic_type.type with -- "sink rule"
    | .inl _ => x86.reorder V r₁ r₂
    | .inr _ => PTX.reorder V r₁ r₂
-/
 := λ _ _ _ => false -- placeholder for now

instance : Arch where
  req := instArchReq
  orderCondition :=  order

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

instance : LitmusSyntax where
  mkRead := mkRead
  mkWrite := mkWrite
  mkFence := mkFence

end Litmus


end Compound
