import Pop

def main : IO Unit := do
  -- let res := Test.inittso12.runWithList Test.testprogram (List.replicate 100 1)
  -- match res with
  --   | Except.error e => IO.println e
  --   | Except.ok s => IO.println s.satisfied

  -- println! s!"running litmus on {Litmus.x86}"
  --let resRaw := Litmus.x86.map $ Litmus.inittso_2.runBFSNoDeadlock
  --println! s!"resRaw : {resRaw}"

  for lit in Litmus.x86_2 do
     println!"litmus: {lit.2.prettyPrint}"
     let res := Litmus.inittso_2.runSearchNoDeadlock lit
     let reslitmus := Util.removeDuplicates $ res.map λ (_,st) => st.outcome
     let outcomes_pretty := String.intercalate "\n" $
       reslitmus.map λ outcome => outcome.prettyPrint
     println! s!"outcomes: \n{outcomes_pretty}"
     println! "-------------"

  for lit in Litmus.x86_4 do
    println!"litmus: {lit.2.prettyPrint}"
    let res := Litmus.inittso_4.runSearchNoDeadlock lit (numWorkers := 7) (batchSize := 15) (breadthFirst := true) (logProgress := true)
    let reslitmus := Util.removeDuplicates $ res.map λ (_,st) => st.outcome
    let outcomes_pretty := String.intercalate "\n" $
      reslitmus.map λ outcome => outcome.prettyPrint
    println! s!" outcomes: \n{outcomes_pretty}"
    println! "-------------"

  --    println! "------"
  --println! s!"{Test.test_iriw_prop_wr}"
  --println! s!"{Test.test_iriw_prop_wr.orderConstraints.lookup Test.test_iriw_prop_wr.system.scopes.systemScope 1 7}"
  --println! s!"{Test.test_iriw_prop_wr.orderConstraints.lookup Test.test_iriw_prop_wr.system.scopes.systemScope 0 7}"
