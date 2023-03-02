-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

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
require std from git "https://github.com/leanprover/std4.git" @ "66dc261"
require Cli from git "https://github.com/mhuisi/lean4-cli.git" @ "5a858c3"
require Murphi from git "https://github.com/goens/lean-murphi.git" @ "e1e6ea7"
