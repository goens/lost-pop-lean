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
