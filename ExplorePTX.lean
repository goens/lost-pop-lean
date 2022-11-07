import Pop
import Pop.Arch.PTX
import Litmus.PTX

open Pop PTX

def main : IO Unit := do
  println! "running PTX 2-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_2
  println! printMultipleLitmusResults mp_litmus (printWitnesses := true)

  println! "running PTX 3-thread tests"
  let mp_litmus := runMultipleLitmus Litmus.tests_3 (maxIterations := some 30000)
  println! printMultipleLitmusResults mp_litmus (printWitnesses := true)

/-
  println! "running PTX 4-thread (IRIW) tests"
  let mp_litmus := runMultipleLitmus Litmus.ptx_4
  println! printMultipleLitmusResults mp_litmus
-/
def litmus := Litmus.WRC_cta_1_2
def state := litmus.initState.applyTrace (litmus.initTransitions ++ litmus.guideTraces.head!.take 8) |>.toOption.get!
def fence := state.requests.getReq! 5
#eval fence.blocksOnPreds
#eval memopsNotDone state fence
#eval state.removed.filter (λ r => r.thread == fence.thread && state.orderConstraints.lookup (state.scopes.reqThreadScope fence) r.id fence.id)

def prev_state := litmus.initState.applyTrace (litmus.initTransitions ++ litmus.guideTraces.head!.take 7) |>.toOption.get!
#eval prev_state.orderConstraints.lookup (prev_state.scopes.reqThreadScope fence) 2 fence.id
