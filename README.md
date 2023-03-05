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
    -h, --help                            Prints this message.
    -a, --arch : String                   Select the target architecture
    --list-archs                          List all available architectures
    -e, --explore                         Automatically explore the litmus
                                          test(s). Default is interactive
                                          exploration
    -b, --batch-size : Nat                Batch size for exploration
    -r, --random-seed : Nat               Random seed for exploration
    -i, --iterations : Nat                Maximum number of iterations
                                          (unlimited if not provided)
    -l, --litmus : String                 Name of a specific litmus test
    -t, --filter-num-threads : Array Nat  Filter litmus tests by given number of
                                          threads
    -p, --partial-trace : Array Nat       Provide a partial (guide) to start the
                                          litmus test
    -w, --print-witnesses                 Print witnesses when exploring
    -A, --axiomatic-alloy                 Generate axomatic version of test in
                                          Alloy format
    -D, --output-dir : String             Output directory
```

## Examples

You can simply run
```
./build/bin/pop
```
This gives you an option to choose an architecture and litmus test manually:
```
Select Architecture. Available:
1. PTX
2. TSO
3. Compound TSO-PTX
4. XC
5. Compound XC TSO
4
Select litmus test. Available:
1: LB_sys : R x; W y(1) || R y; W x(1)
2: SB_sys : W x(1); R y || W y(1); R x
3: MP_sys : W x(1); W y(1) || R y; R x
4: MP_sys_F : W x(1); Fence.sys_sc; W y(1) || R y; Fence.sys_sc; R x
5: SB_sys_F : W x(1); Fence.sys_sc; R y || W y(1); Fence.sys_sc; R x
6: MP_cta_F : W x(1); Fence.cta_sc; W y(1) || R y; Fence.cta_sc; R x
  where sys := [[0, 1] = [0], [1]]
7: IRIW_sys : W x(1) || R x; R y || R y; R x || W y(1)
8: IRIW_sys_F : W x(1) || R x; Fence.sys_sc; R y || R y; Fence.sys_sc; R x || W y(1)
1
======================================
LB_sys, program state:
R x; W y(1) || R y; W x(1)
scopes : {[0, 1]}
--------------------------------------
Current state:
requests:
 Request 0 W x(0) : [propagated to [0, 1], origin thread : 0, pred. at : []],
 Request 1 W y(0) : [propagated to [0, 1], origin thread : 0, pred. at : []]

 T0                      || T1                      |
----------------------------------------------------

removed: []
satisfied: []
constraints:

--------------------------------------
Current trace:
[]
--------------------------------------
Possible transitions:
0: Undo (last transition)
1: Accept (R y)
2: Accept (R x)
```

You can also choose the architecture and litmus test from the command line, as well as part of the trace (selections) from the command. For example, to run the compound litums test named 'MP_writes_tso_ptx_acq_cta' and accept the first option for the first four transitions (which results in the litmus test accepting all four requests first), you can run the following:

```
 ./build/bin/pop -a Compound -l MP_writes_tso_ptx_acq_cta -p 1,1,1,1.
```
This allows you to explore the litmus test manually from there by choosing options:
```
======================================
MP_writes_tso_ptx_acq_cta, program state:
 ||
scopes : {[1]PTX, [0]x86, [0, 1]x86+PTX}
--------------------------------------
Current state:
requests:
 Request 0 W x(0) : [propagated to [0, 1], origin thread : 0, pred. at : [1]],
 Request 1 W y(0) : [propagated to [0, 1], origin thread : 0, pred. at : []],
 Request 2 R.cta_acq y : [propagated to [1], origin thread : 1, pred. at : []],
 Request 3 R x : [propagated to [1], origin thread : 1, pred. at : []],
 Request 4 W x(1) : [propagated to [0], origin thread : 0, pred. at : []],
 Request 5 W y(1) : [propagated to [0], origin thread : 0, pred. at : []]

 T0                      || T1                      |
----------------------------------------------------
 4[W x 1]                || 2[R. cta_acq y]         |
 5[W y 1]                || 3[R x]                  |

removed: []
satisfied: []
constraints (scope [1]) : {0[W x 0]} → {1[W y 0], 4[W x 1], 5[W y 1], 3[R x]};   {1[W y 0]} → {4[W x 1], 5[W y 1], 2[R. cta_acq y]};   {4[W x 1]} → {5[W y 1]};   {2[R. cta_acq y]} → {3[R x]}
constraints (scope [0]) : {0[W x 0]} → {1[W y 0], 4[W x 1], 5[W y 1], 3[R x]};   {1[W y 0]} → {4[W x 1], 5[W y 1], 2[R. cta_acq y]};   {4[W x 1]} → {5[W y 1]}
constraints (scope [0, 1]) : {0[W x 0]} → {1[W y 0], 4[W x 1], 5[W y 1], 3[R x]};   {1[W y 0]} → {4[W x 1], 5[W y 1], 2[R. cta_acq y]};   {4[W x 1]} → {5[W y 1]}
--------------------------------------
Current trace:
[1, 1, 1, 1]
--------------------------------------
Possible transitions:
0: Undo (last transition)
1: Propagate Req2 (R.cta_acq y) to Thread 0
2*: Propagate Req3 (R x) to Thread 0
3: Propagate Req4 (W x(1)) to Thread 1
```
If the litmus test has a trace hint, as is the case here, the options in the trace are marked with a `*`. Here it coincides with the partial trace we gave it and continues with transition `2*: Propagate Req3 (R x) to Thread 0 `). In this case, if we follow the trace hint until the end, we get a result allowing the behavior in this litmus test:
```
=========================
=======  SUMMARY  =======
=========================
hint for MP_writes_tso_ptx_acq_cta := [Accept (R. cta_acq y) at Thread 1, Accept (R x) at Thread 1, Accept (W x 1) at Thread 0, Accept (W y 1) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 5]
  Outcome: y = 1; x = 0
  Expected: y = 1; x = 0 (✓)
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

You can also run multiple tests at the same time (and in parallel) if you choose by specifying multiple litmus tests explicitly:
```
./build/bin/pop -a PTX -t 2,3 -e -l WRC_sc_dep,WRC_two_deps -i 100000
```
or by specifying the numbers of threads to filter:
```
./build/bin/pop -a Compound -t 2,3 -e
```
