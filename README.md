# POP - Lean

This repository contains the Lean4 implementation of the LOST-POP model.

# Building

To build this repository, you need Lean4, which you can set up [here](https://leanprover.github.io/lean4/doc/quickstart.html).
With Lean4 installed you can build the project by running
```
lake update && lake build
```

# Running

After compiling, you should be able to run the executable with the interactive mode by running
```
/build/bin/pop
```

An automatic exploration, among other options, can be configured using the command following flags:
```
  -h, --help                            Prints help message.
  -a, --arch : String                   Select the target architecture
  --list-archs                          List all available architectures
  -e, --explore                         Automatically explore the architecture
  -b, --batch-size : Nat                Batch size for exploration
  -r, --random-seed : Nat               Random seed for exploration
  -i, --iterations : Nat                Maximum number of iterations (unlimted
                                        if not provided)
  -l, --litmus : String                 Name of a specific litmus test
  -t, --filter-num-threads : Array Nat  Print witnesses when exploring
```
