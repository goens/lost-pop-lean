import Pop.Util
import Pop.States
import Pop.Program
import Pop.Litmus

namespace Test

open Util Pop Litmus Transition

def trace := [acceptRequest (mkRead 0) 0, acceptRequest (mkWrite 0 0) 0]
def trace2 := [acceptRequest (mkRead 0) 0, acceptRequest (mkWrite 0 0) 1, propagateToThread 0 1, propagateToThread 1 0, satisfyRead 0 1]

-- def res := printResult $ inittso12.applyTrace trace
-- def res2 := printResult $ inittso12.applyTrace trace2


def testprogram := {| R x || W y=1; W x=2 |}


def testaccept := inittso_2.applyAcceptRequest (mkRead 0) 0
    -- let scope := testaccept.system.scopes.jointScope 0 req.thread
    -- let pred := testaccept.orderConstraints.predecessors scope 0 (reqIds testaccept.requests)
    -- let reqOps := testaccept.requests.val.filter (λ req => match req with | none => false | some r => pred.elem r.id)
    -- let reqs := filterNones reqOps.toList
    -- let predPropagated := reqs.map (λ r => r.fullyPropagated state.system.scopes.systemScope)
    -- unpropagated || predPropagated.foldl (. && .) true
-- #eval inittso12.system.threads
--#eval testaccept.toOption.get!.canPropagate 0 1

def test_iriw := (inittso_4.applyTrace! Litmus.IRIW.1).applyTrace! $ List.join $ Litmus.IRIW.2.map (Array.toList) |>.toList
--#eval test_iriw
--#eval test_iriw.applyTrace $ mkPropagateTransitions [7] [1]
def test_iriw_prop_wr  := test_iriw.applyTrace! $ mkPropagateTransitions [7] [0,1,2]

-- #eval test_iriw_prop_wr.orderConnstraints state.system.scopes.system_scope 1 7
-- #eval test_iriw_prop_wr.orderConnstraints state.system.scopes.system_scope 0 7

def mp_1_0_trace := [Litmus.MP.2[1][0], Litmus.MP.2[1][0]] ++ [Transition.propagateToThread 3 0, Transition.satisfyRead 3 0, Litmus.MP.2[0][0], Litmus.MP.2[0][1]] -- ++ (mkPropagateTransitions [4,5] [1]) ++ [Transition.propagateToThread 2 0] --, Transition.satisfyRead 2 1]
def mp_1_0 := (inittso_2.applyTrace! Litmus.MP.1).applyTrace! mp_1_0_trace
#eval mp_1_0 --.possibleTransitions #[]
def mp_accepts := List.join $ Litmus.MP.2.map (Array.toList) |>.toList
def test_mp := (inittso_2.applyTrace! Litmus.MP.1).applyTrace! mp_accepts
#eval test_mp
def test_mp2 := test_mp.applyTrace! $ mkPropagateTransitions [4,5] [0]
def test_mp3 := test_mp2.applyTrace! $ mkPropagateTransitions [2,3] [1]



end Test
