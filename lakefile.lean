import Lake
open Lake DSL

package pop {
  -- add package configuration options here
}

lean_lib Pop {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe pop_arm {
  root := `InteractARM
}

lean_exe pop_x86 {
  root := `InteractTSO
}

lean_exe pop_explore_x86 {
  root := `ExploreTSO
}

lean_exe pop_explore_arm {
  root := `ExploreARM
}
