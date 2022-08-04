import Pop.States

open Pop

inductive DefaultReqType
  | mk : DefaultReqType
  deriving BEq, Inhabited

instance : ArchReq where
  type := DefaultReqType
  beq_inst := instBEqDefaultReqType
  inhabited_inst := instInhabitedDefaultReqType

def tso_reorder : Request → Request → Bool
  | r₁, r₂ => if r₁.isBarrier || r₂.isBarrier
  then false
  else
  let sc_per_loc := r₁.address? != r₂.address?
  --dbg_trace s!"sc_per_loc: {sc_per_loc}"
  let ppo := (r₁.thread != r₂.thread) || !(r₂.isWrite && r₁.isRead)
  --dbg_trace s!"ppo: {sc_per_loc}"
  if sc_per_loc then ppo else false
  -- TODO: satisfied but not deleted?

def tso_propagate : SystemState → RequestId → ThreadId → Bool
  | st, reqId, _ =>
    let sscope := st.scopes.systemScope
    let pred := st.orderPredecessors sscope reqId
    st.idsToReqs pred |>.all λ req => req.fullyPropagated sscope

instance : Arch where
  req := instArchReq
  acceptConstraints := λ _ _ _ => true
  propagateConstraints := tso_propagate
  satisfyReadConstraints := λ _ _ _ => true
  reorderCondition :=  tso_reorder
