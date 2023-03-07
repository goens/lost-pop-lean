# LOST-POP - Lean

This repository contains the Lean4 implementation of the LOST-POP model.

# Artifact

This README is found on the artifact for the PLDI'23 submission "Compound Memory Models". This artifact can be run from a docker container or built and executed locally.

## Docker

To execute this from within a docker container, start an instance of the docker image in the artifact. This can be done from within the GUI e.g. in Windows/MacOS or in Linux e.g. with:
```shell
sudo docker run -it $THIS_DOCKER_IMAGE /usr/bin/bash
```
From within the image, to run these models just go to the corresponding folder and run the script that executes them all:
```shell
cd /home/user/models
./run-all-litmus.sh
```

To run individual files, see [Running](#Running) and the [examples](#examples) below.

## Native installation

You can also install and run this repository in your native environment, without docker. You will need to have some dependencies installed in your machine:
 - Lean4, see [here](https://leanprover.github.io/lean4/doc/quickstart.html).
 - git, e.g. by `sudo apt install git` in Debian-based systems like Debian or Ubuntu.
 - Optional: A java runtime environment for running alloy and axiomatic tests, e.g. by `sudo apt install openjdk-16-jdk` in Debian-based systems.
 - Optional: R and dplyr for running the analysis in the end. You can get this e.g. by running the following in a Debian-based system:
  ```shell
  sudo apt install r-base
  Rscript -e "install.packages(c('dplyr','readr'), repos='https://cran.rstudio.com')"
  ```

Once you have everything installed, you can first clone this repository and all its dependencies:
```shell
git clone --branch PLDI-AE git@github.com:goens/pop-lean.git --recursive
```
You can then run everything with the script given here:
```shell
./run-all-litmus.sh
```
To run individual litmus tests, see [Running](#Running) and the [examples](#examples) below.

# Building

To build this repository, you need Lean4, which you can set up [here](https://leanprover.github.io/lean4/doc/quickstart.html).
With Lean4 installed you can build the project by running
```shell
lake update && lake build
```

# Running

After compiling, you should be able to run the executable with the interactive mode by running
```shell
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
```shell
./build/bin/pop
```
This gives you an option to choose an architecture and litmus test manually:
```shell-session
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

```shell
 ./build/bin/pop -a Compound -l MP_writes_tso_ptx_acq_cta -p 1,1,1,1.
```
This allows you to explore the litmus test manually from there by choosing options:
```shell-session
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
```shell-session
=========================
=======  SUMMARY  =======
=========================
hint for MP_writes_tso_ptx_acq_cta := [Accept (R. cta_acq y) at Thread 1, Accept (R x) at Thread 1, Accept (W x 1) at Thread 0, Accept (W y 1) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 5]
  Outcome: y = 1; x = 0
  Expected: y = 1; x = 0 (✓)
```

You can also let the tool automatically explore a litmus test automatically. If we consider the test 'MP_writes_tso_ptx_acq_sys' we can explore it by running:
```shell
./build/bin/pop -a PTX -l ISA2_fences_rel -e -i 10000
```

Which will run this for 10000 iterations. We get the result:
```shell-session
Exploring PTX: 1 tests with [2, 3, 4] threads, with batch size 6, maximum 10000 iterations...
| Litmus test      | Axiomatic | POP |
--------------------------------------
| ISA2_fences_rel  | ✓         | 𐄂?  |
```

In this case, 10000 iterations is not enough to exhaustively explore the design space; the summary results returns `𐄂?` for the operational model. It means it could not find a witness within the given number of iterations. The litmus test is probably disallowed. If we leave out `-i 10000` option, the command will run until it finishes.
```shell-session
❯ time ./build/bin/pop -a PTX -l ISA2_fences_rel -e`
Exploring PTX: 1 tests with [2, 3, 4] threads, with batch size 6, unlimited iterations...
```

**CAUTION**: For larger litmus tests (especially those with 4 threads), without a maximum number of iterations, this command will probably not finish in any reasonable amount of time. We recommend always adding a timeout.

You can also run multiple tests at the same time (and in parallel) if you choose by specifying multiple litmus tests explicitly:
```shell
./build/bin/pop -a PTX -t 2,3 -e -l WRC_sc_dep,WRC_two_deps -i 100000
```
or by specifying the numbers of threads to filter:
```shell
./build/bin/pop -a Compound -t 2,3 -e
```

# Specifying your own Litmus tests

You can specify your own Litmus test by adding it to the corresponding file in `Litmus/ARCH.lean`. For example, to add a Compound x86TSO-PTX test we add it to `Litmus/Compound.lean`.

## Basic Syntax
The LOST-POP implementation has custom syntax to define litmus tests more simply, for example, consider the following message passing litmus test:
```
deflitmus MP := {|  W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0 |}
```

The `deflitmus` keyword is used in general to define a new litmus test, followed by the name of the litmus test and the `:=`. Enclosed by the brackets `{|` and `|}` we can specify the operations of the litmus test:
  - A write with the syntax `W <variable> = <value>`
  - A read with the syntax `R <variable> // <expected value>`
  - A fence with the syntax `Fence`.
Multiple instructions in a thread are separated by `;`, and the different threads are separated by `||`. The example above thus has two threads, each executing three instructions (write, fence, write and read, fence, read respectively).

## Annotations

Most of the time, a litmus test needs precise annotations for the instructions it uses, like the type of a fence. This can also be added to a Litmus test, as follows:
 - Writes: `W. <annotations> <variable> = <value>`
 - Reads: `R. <annotations> <variable> // <expected value>`
 - Fences: `Fence. <annotations>`
 - Dependencies: These are annotated on the semicolon separating the two instructions: `<instruction1> ;dep <instruction2>`
 For example, consider the following WRC litmus test for PTX:
```
deflitmus WRC := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|} ✓
```
Here, the `R. sys_acq` marks that read as a system-scoped acquire read, and the `;dep`separator on the other thread marks a dependency between the read of `y` and the read of `x`.

You can also add an annotation at the end of the litmus test that tells what the expected (axiomatic) behavior is for this test, either `✓` (allowed) or `𐄂` (disallowed).

## Compound Systems and Scopes

We can use this syntax to describe the system, including different scopes and architectures.
The syntax is ``` where sys := <system description>` and the system description are nested blocks of threads enclosed in `{` and `}`, with the thread names. For example
```
deflitmus MP_writes_tso := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. x86, {T1}. PTX}
```
This litmus test describes a heterogeneous litmus test with x86 and PTX threads. On the other hand, the following PTX litmus test has threads in different CTAs:
```
deflitmus IRIW_3ctas_1scoped_w := {| W. cta_rlx x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ✓
```

Note that the (axiomatic) allowed/disallowed annotations now go after this system description.

# Defining new Architectures

To define a new architecture, we need to add an implementation in:
`Pop/Arch/<NEWARCH>.lean` and then add it to the `Pop/Arch.lean` file, like the other architectures.

The architecture in the model is described by two [typeclasses](https://leanprover.github.io/functional_programming_in_lean/type-classes/pos.html#classes-and-instances), `ArchReq` and `Arch`:
```lean
class ArchReq where
  (type : Type 0)
  (instBEq : BEq type)
  (instInhabited : Inhabited type)
```
The `ArchReq` typeclass marks a type as being a type of request, it has to have an instance of boolean equality `BEq` and `Inhabited`, as well as a `ToString` instance for printing.

The `Arch` typeclass, on the other hand, describes the architecture itself:
```lean
class Arch where
  (req : ArchReq)
  (orderCondition : ValidScopes → Request → Request → Bool)
  (blockingSemantics : Request → BlockingSemantics)
  (scopeIntersection : (valid : ValidScopes) → Request → Request → @Scope valid := λ v _ _ => v.systemScope)
```

It builds upon the request type `req`, and adds an `orderCondition`, a `blockingSemantics`, which is a list of `BlockingKinds`:
```lean
inductive BlockingKinds
  | Read2ReadPred
  | Read2ReadNoPred
  | Read2WritePred
  | Read2WriteNoPred
  | Write2Read
  | Write2Write

abbrev BlockingSemantics := List BlockingKinds
```
Finally, an optional architecture-specific `scopeIntersection` function can be specified here as well.

## Litmus Syntax

To define your own litums tests in your self-defined architecture, there is an additional typeclass:
```lean
class LitmusSyntax where
  mkRead : String → Address → String → BasicRequest
  mkRMW : String → Address → String → BasicRequest × BasicRequest
  mkWrite : String → Address → Value → String → BasicRequest
  mkFence : String → String → BasicRequest
```

This typeclass tells you how to build your own `ReqType` from the annotation strings and other values (like `Address`es and `Value`s).
