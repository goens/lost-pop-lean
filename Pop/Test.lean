import Pop.Util
import Pop.States
import Pop.Program

namespace Test

open Util Pop


theorem proof1 : List.sublist [0] [0,1] := by simp
theorem proof2 : List.sublist [1] [0,1] := by simp
open ListTree in
def scopes12 : ListTree ThreadId [0,1] :=  parentCons (ListTree.leaf [1]) (parentCons (ListTree.leaf [0]) (parentNil [0,1]) proof1) proof2

def valid_scopes12 : ValidScopes := { system_scope := [0,1], scopes := scopes12, threads_in := sorry}

def tso_reorder : Request → Request → Bool
  | r₁, r₂ => if r₁.isBarrier || r₂.isBarrier
     then false
     else
       let sc_per_loc := r₁.address? == r₂.address? && r₁.address? != none
       let ppo := (r₁.thread != r₂.thread) || (r₂.isWrite && r₁.isRead)
       sc_per_loc || ppo
  -- TODO: satisfied but not deleted?
def tso12 : System := { scopes := valid_scopes12, reorder_condition := tso_reorder}

def inittso12 : SystemState := SystemState.init tso12

open Transition

def trace := [acceptRequest (mkRead 0) 0, acceptRequest (mkWrite 0 0) 0]
def trace2 := [acceptRequest (mkRead 0) 0, acceptRequest (mkWrite 0 0) 1, propagateToThread 0 1, propagateToThread 1 0, satisfyRead 0 1]

-- def res := printResult $ inittso12.applyTrace trace
-- def res2 := printResult $ inittso12.applyTrace trace2


def testprogram := <| R x || W y=1; W x=2 |>
#eval testprogram.toString


def testaccept := inittso12.applyAcceptRequest (mkRead 0) 0
#eval testaccept.canPropagate 0 1
#eval testaccept.requests.val[0].get!.isPropagated 1
#eval testaccept.requests.val[0]
    -- let scope := testaccept.system.scopes.jointScope 0 req.thread
    -- let pred := testaccept.orderConstraints.predecessors scope 0 (reqIds testaccept.requests)
    -- let reqOps := testaccept.requests.val.filter (λ req => match req with | none => false | some r => pred.elem r.id)
    -- let reqs := filterNones reqOps.toList
    -- let predPropagated := reqs.map (λ r => r.fullyPropagated state.system.scopes.systemScope)
    -- unpropagated || predPropagated.foldl (. && .) true
-- #eval inittso12.system.threads
--#eval testaccept.toOption.get!.canPropagate 0 1

end Test
