import Lake
open Lake DSL

package pop {
  -- add package configuration options here
}

lean_lib Pop {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe pop {
  root := `Main
}
