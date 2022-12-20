import Lake
open Lake DSL

package pop {
  -- add package configuration options here
}

lean_lib Pop {
  -- add library configuration options here
}

lean_lib Litmus {
  -- add library configuration options here
}

@[default_target]
lean_exe pop {
  root := `Main
}

lean_exe pop_explore_x86 {
  root := `ExploreTSO
}

lean_exe pop_explore_arm {
  root := `ExploreARM
}

lean_exe pop_explore_ptx {
  root := `ExplorePTX
}

lean_exe pop_explore_compound {
  root := `ExploreCompound
}

lean_exe alloy {
  root := `GenerateAlloy
}

require std from git "https://github.com/leanprover/std4.git" @ "main"
require Cli from git "https://github.com/mhuisi/lean4-cli.git" @ "nightly"
require Murphi from git "https://github.com/goens/lean-murphi.git" @ "e1e6ea7"

