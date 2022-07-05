import Pop.Test
import Pop.Program
import Pop.Util
import Pop.Litmus

def main : IO Unit := do
  -- let res := Test.inittso12.runWithList Test.testprogram (List.replicate 100 1)
  -- match res with
  --   | Except.error e => IO.println e
  --   | Except.ok s => IO.println s.satisfied

  -- println! s!"running litmus on {Litmus.x86}"
  --let resRaw := Litmus.x86.map $ Litmus.inittso_2.runBFSNoDeadlock
  --println! s!"resRaw : {resRaw}"
  for lit in Litmus.x86 do
      let res := Litmus.inittso_2.runBFS lit (λ st => st.satisfied.length > 1) (stopAtCondition := false)
      let reslitmus := Util.removeDuplicates $ res.map λ (_,st) => st.outcome
      let outcomes_clean := reslitmus.map λ outcome => outcome.map λ (thread,(addr,val)) => val
      println! s!" outcomes: {outcomes_clean}"
      println! "-------------"
  --    println! "------"
  --println! s!"{Test.test_iriw_prop_wr}"
  --println! s!"{Test.test_iriw_prop_wr.orderConstraints.lookup Test.test_iriw_prop_wr.system.scopes.systemScope 1 7}"
  --println! s!"{Test.test_iriw_prop_wr.orderConstraints.lookup Test.test_iriw_prop_wr.system.scopes.systemScope 0 7}"
