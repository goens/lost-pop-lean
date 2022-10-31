import Pop
import Pop.AxiomaticAlloy
import Pop.Arch

open Pop
def main : IO Unit := do
  let some arch ← selectArchitecture (← IO.getStdin)
    | return ()
  for litmus in arch.getLitmusTests do
    let outputDir : System.FilePath := "generated_litmus" / s!"{arch}/"
    IO.FS.createDirAll outputDir
    let outputFile := outputDir / (@Litmus.Test.name arch.getInstArch litmus ++ ".als")
    IO.FS.writeFile outputFile $ @toAlloyLitmus arch.getInstArch arch.getInstLitmusSyntax litmus
