import Pop
import Pop.Arch.PTX
import Pop.AxiomaticAlloy
import Litmus.PTX

open Pop PTX

def outputFile := "generated_litmus.als"

def main : IO Unit := do
  let exceptLitmus ← selectLitmusLoop Litmus.allPTX (← IO.getStdin)
  match exceptLitmus with
    | .error msg => println! msg
    | .ok litmus => IO.FS.writeFile outputFile $ toAlloyLitmus litmus
