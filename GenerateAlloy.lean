import Pop
import Pop.AxiomaticAlloy
import Pop.Arch

open Pop
def main : IO Unit := do
  for arch in ArchType.available do
    let tests := arch.getLitmusTests
    IO.println s!"generating {tests.length} tests for {arch}"
    for litmus in tests do
      let outputDir : System.FilePath := "alloy_generated" / s!"{arch}/"
      IO.FS.createDirAll outputDir
      let outputFile := outputDir / (@Litmus.Test.name arch.getInstArch litmus ++ ".als")
      IO.FS.writeFile outputFile $ @toAlloyLitmus arch.getInstArch arch.getInstLitmusSyntax litmus
