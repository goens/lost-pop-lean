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

@[defaultTarget]
lean_exe pop_arm {
  root := `InteractARM
}

lean_exe pop_x86 {
  root := `InteractTSO
}

lean_exe pop_ptx {
  root := `InteractPTX
}

lean_exe pop_compound {
  root := `InteractCompound
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

require std from git "https://github.com/leanprover/std4.git" @ "66b5f95c7f8632823a2d8fd57c54e3c02dead2df"
