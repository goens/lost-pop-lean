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
require std from git "https://github.com/leanprover/std4.git" @ "v4.7.0"
require Cli from git "https://github.com/mhuisi/lean4-cli.git" @ "v2.2.0-lv4.0.0"
require Murphi from git "https://github.com/goens/lean-murphi.git" @ "1a5794d23923fb7fd57cc45cfd44c6da3588f31b"
