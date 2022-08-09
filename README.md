# POP - Lean

This repository contains the Lean4 implementation of the (generalized, scoped) POP model.

# Building

To build this repository, you need Lean4, which you can set up [here](https://leanprover.github.io/lean4/doc/quickstart.html).
With Lean4 installed you can build the project by running
```
$> lake build
```

# Running

After compiling, you should be able to run the executable with the interactive mode by running
```
/build/bin/pop
```

# Exploration

I plan to add a CLI in the future, for now, if you want to try out the exploration part, there's code commented out in `Main.lean`
