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
build/bin/pop
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

## Examples

For example, to run the compound litums test named 'MP_writes_tso_ptx_acq_cta' you can run the following:

```
./build/bin/pop -a Compound -l MP_writes_tso_ptx_acq_cta
```

You can also let the tool automatically explore a litmus test automatically. If we consider the test 'MP_writes_tso_ptx_acq_sys' we can explore it by running:
```
❯ ./build/bin/pop -a PTX -l ISA2_fences_rel -e -i 10000
```

Which will run this for 10000 iterations. We get the result:
```
Exploring PTX: 1 tests with [2, 3, 4] threads, with batch size 6, maximum 10000 iterations...
| Litmus test      | Axiomatic | POP |
--------------------------------------
| ISA2_fences_rel  | ✓         | 𐄂?  |
```

In this case, 10000 iterations is not enough to exhaustively explore the design space; the summary results returns `𐄂?` for the operational model. It means it could not find a witness within the given number of iterations. The litmus test is probably disallowed. If we leave out `-i 10000` option, the command will run until it finishes.
```
❯ time ./build/bin/pop -a PTX -l ISA2_fences_rel -e`
Exploring PTX: 1 tests with [2, 3, 4] threads, with batch size 6, unlimited iterations...
```

~~~
**CAUTION**: For larger litmus tests (especially those with 4 threads), without a maximum number of iterations, this command will probably not finish in any reasonable amount of time. We recommend always adding a timeout.
~~~
