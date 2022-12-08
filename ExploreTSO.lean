import Pop
import Pop.Arch.TSO
import Litmus.TSO

open Pop x86
open Litmus

def main : IO Unit := do
  println! "running TSO 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_2
  println! printMultipleLitmusResults mp_litmus

  println! "running TSO 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_3 (maxIterations := some 100000)
  println! printMultipleLitmusResults mp_litmus

  println! "running TSO 4-thread tests"
  let mp_litmus := runMultipleLitmus [Litmus.IRIW] (maxIterations := some 100000)
  println! printMultipleLitmusResults mp_litmus (printWitnesses := true)

-- testing
-- def test := x86.Litmus.two_rmws
-- def initState := test.initState.applyTrace! test.initTransitions
-- def allaccepts := initState.applyTrace! $ test.program.allFilter (λ _ => true)
-- def state := allaccepts.applyTransition! (allaccepts.possibleTransitions #[]).head!
-- def read := state.requests.getReq? 1 |>.get!
-- def readThreadRequests := state.requests.filter (·.thread == read.thread)
-- def ocLookup := state.orderConstraints.lookup (state.scopes.reqThreadScope read)
-- def afterRead := readThreadRequests.filter
--              λ req => ocLookup read.id req.id -- && readThreadRequests.all
--                --λ req' => ocLookup req.id req'.id
-- #eval state
-- #eval readThreadRequests.map Request.id
-- #eval afterRead
-- #eval state.atomicWriteAfterRead 1
-- #eval state.applyTransition! state.possibleSatisfyTransitions.head! |>.requests
