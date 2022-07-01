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
  -- let resRaw := Litmus.x86.map $ Test.inittso_2.runDFSNoDeadlock
  -- for res in resRaw do
  --    let reslitmus := Util.removeDuplicates $ res.map λ (_,st) => st.outcome
  --    println! reslitmus
  --    println! "------"
  println! s!"{Test.test_iriw_prop_wr}"
  println! s!"{Test.test_iriw_prop_wr.orderConstraints Test.test_iriw_prop_wr.system.scopes.systemScope 1 7}"
  println! s!"{Test.test_iriw_prop_wr.orderConstraints Test.test_iriw_prop_wr.system.scopes.systemScope 0 7}"