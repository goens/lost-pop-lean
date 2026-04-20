# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is **LOST-POP**: a Lean 4 implementation of the LOST-POP operational memory model, as described in the PLDI '23 paper "Compound Memory Models". It models how memory operations (reads, writes, fences, RMW atomics) propagate and become visible across threads under various hardware memory models.

## Build and Run Commands

```bash
# Fetch dependencies and build
lake update && lake build

# Run interactively (select arch and litmus test via prompts)
lake exe pop

# Run with specific architecture and litmus test
lake exe pop -a TSO -l SB

# Automatic exploration with iteration limit
lake exe pop -a PTX -l ISA2_fences_rel -e -i 10000

# Explore all tests for an architecture (by thread count filter)
lake exe pop -a Compound -t 2,3 -e

# Generate Alloy axiomatic output
lake exe pop -a TSO -A

# Run everything (build + explore TSO/PTX/Compound + generate Alloy)
./runall.sh
```

Available architectures (via `-a`): `PTX`, `TSO`, `ARM`, `XC`, `SC`, `Compound` (TSO+PTX), `XCTSO` (XC+TSO)

## Architecture and Code Structure

### Core Model (`Pop/`)

- **`Pop/States.lean`** — Foundational types: `RequestId`, `ThreadId`, `Address`, `Value`, `Request`, `SystemState`. A `SystemState` holds the request array, order constraints, scope hierarchy, and satisfaction tracking.

- **`Pop/Pop.lean`** — The operational model transitions:
  - `Transition` inductive: `acceptRequest`, `propagateToThread`, `satisfyRead`, `dependency`
  - `SystemState.canApplyTransition` / `applyTransition` — guards and application of transitions
  - Fence blocking logic via `BlockingKinds` (Read2ReadPred, Write2Write, etc.)
  - RMW/atomic handling: `cleanupTransactions`, `validateWrite`

- **`Pop/Exploration.lean`** — Automatic state-space exploration: random trace generation, batch exploration, result aggregation via `runMultipleLitmus` / `printMultipleLitmusResults`.

- **`Pop/Interactive.lean`** — Interactive REPL loop for manual exploration.

- **`Pop/Litmus.lean`** — `Litmus.Test` structure (program, expected outcome, guide traces, axiomatic result), and `SystemState.partialOutcome` to check outcomes.

- **`Pop/AxiomaticAlloy.lean`** — Alloy model generation for axiomatic cross-validation.

- **`Pop/Arch.lean`** — `Arch` typeclass with hooks: `orderCondition`, `blockingSemantics`, `propagateConstraints`, `acceptConstraints`, `satisfyReadConstraints`, plus effect hooks (`acceptEffects`, `propagateEffects`, `satisfyReadEffects`).

### Architecture Implementations (`Pop/Arch/`)

Each architecture implements the `Arch` typeclass. The pattern is:
1. Define an `inductive Req` for architecture-specific request metadata
2. Implement `orderCondition` (what ordering between requests is enforced)
3. Implement `blockingSemantics` (which `BlockingKinds` a fence-like request carries)
4. Optionally override constraint/effect hooks for arch-specific behavior

Compound architectures (e.g., `Pop/Arch/Compound.lean`) compose two architectures and add scope-awareness — threads belong to sub-scopes (e.g., PTX CTAs, x86 cores) with different visibility rules per scope.

### Litmus Tests (`Litmus/`)

Each file (e.g., `Litmus/TSO.lean`) defines litmus tests using a DSL with `mkRead`, `mkWrite`, `mkFence`, `mkRMW` helpers and a macro/elaborator that builds `Litmus.Test` values. Tests specify:
- The program as a list of per-thread instruction sequences
- The `expected` outcome (which reads return which values)
- `axiomaticAllowed` (`yes`/`no`/`unknown`)
- Optional `guideTraces` (witness traces that demonstrate allowed behaviors)

### Entry Point

`Main.lean` wires CLI flags (via the `Cli` library) to three modes: `interact`, `explore`, and `alloy`. `Pop/Arch.lean` provides `ArchType` enum and dispatches to each architecture's `instArch` instance.

## Key Concepts

- **Scope hierarchy**: Requests belong to threads, threads to scopes (e.g., CTA, system). Order constraints are scope-tagged. `ValidScopes` tracks the scope tree.
- **Order constraints**: A `RequestId × RequestId` DAG per scope, used for coherence and fence blocking.
- **Predecessors**: Writes to address `x` that have propagated to a thread become "predecessors" of subsequent reads there, affecting fence semantics.

## Proof Architecture Plan

The codebase is being extended with a formal proof layer. The computational code (`Pop/Pop.lean`, `Exploration.lean`, etc.) remains the reference implementation; the proof layer adds an inductive LTS relation on top of it and works toward a verified model checker. The work is organised into five phases.

### Phase 0 — Remove `removedCoherent` from the computational code
Drop the `removedCoherent` field from `SystemState` and remove every `removedCoherent := sorry` from construction sites in `Pop/Pop.lean`. The property it was approximating (ids in `removed` were once in `requests`) will reappear in Phase 5 as a field of `WellFormed`, where it can be proved properly. This is a pure structural cleanup with no semantic change.

### Phase 1 — Core LTS: `Pop/LTS.lean` (new file)
Introduce a joint state structure that pairs the program state with the system state:
```lean
structure LTSState [Arch] where
  prog : ProgramState
  sys  : SystemState
```
`LTSState` replaces the ad-hoc `(ProgramState, SystemState)` pairs currently threaded through `Exploration.lean` and `Interactive.lean`; those files are updated to use it.

Define the labelled transition system relation (Option B — result state explicit via an equation):
```lean
inductive LostPOP [Arch] : Transition → LTSState → LTSState → Prop
  | accept {σ σ'} {req} {tId}
      (h_can  : σ.sys.canAcceptRequest req tId)
      (h_step : σ' = ...)   -- consumes from σ.prog, updates σ.sys
      : LostPOP (.acceptRequest req tId) σ σ'
  | propagate ...  -- prog unchanged
  | satisfy   ...  -- prog unchanged
  | dependency ... -- prog unchanged
```

Move the `possibleTransitions` logic (currently split across `Exploration.lean` and the `canApply*` predicates in `Pop.lean`) into this file and prove the key invariant:
```
t ∈ σ.possibleTransitions ↔ ∃ σ', LostPOP t σ σ'
```

Also prove: determinism (`LostPOP t σ σ₁ → LostPOP t σ σ₂ → σ₁ = σ₂`) and the equivalence with the existing computation (`LostPOP t σ σ' ↔ σ.sys.canApplyTransition t ∧ σ' = ...`).

Define reachability and litmus test outcomes:
```lean
def Reachable [Arch] := Relation.ReflTransGen (fun σ σ' => ∃ t, LostPOP t σ σ')

def Allowed   [Arch] (test : Litmus.Test) : Prop := ∃ σ', Reachable (initState test) σ' ∧ ...
def Forbidden [Arch] (test : Litmus.Test) : Prop := ¬ Allowed test
```

### Phase 2 — Finiteness and verified model checking
Prove that for a fixed initial `LTSState`, the set of states reachable via `Reachable` is finite. The argument has three parts:
- `accept` transitions are bounded by the total instruction count of `prog` (each instruction is consumed exactly once)
- once all accepts are issued, the request set is fixed and finite
- `propagate` and `satisfy` transitions grow monotonically toward finite bounds (`propagated_to` lists, satisfaction pairs)

From finiteness, `Reachable` is decidable, giving a verified model checker for `Allowed`/`Forbidden`. Prove the existing exploration engine in `Exploration.lean` sound and complete with respect to `Reachable`.

### Phase 3 — `ValidScopes` invariants
Restore the commented-out fields (`system_scope_is_scope`, `scopes_consistent`) to `ValidScopes` and prove the `valid` field in `systemScope`. Resolve the `valid := sorry` in `jointScope` — either from a strengthened `ValidScopes` structure or deferred to `WellFormed` in Phase 5.

### Phase 4 — `Arch` typeclass for proofs
Introduce an optional `ArchProps` extension typeclass carrying mathematical properties needed by specific theorems (e.g., acyclicity of `orderCondition`, monotonicity of `blockingSemantics` with respect to scope inclusion). Driven by what Phase 2 proofs actually require; not a hard prerequisite for earlier phases.

### Phase 5 — `WellFormed` invariant
Define:
```lean
structure WellFormed [Arch] (σ : LTSState) : Prop where
  removedCoherent      : ∀ r ∈ σ.sys.removed, r.id ∈ ...
  jointScopeExists     : ...   -- if not resolved in Phase 3
  orderConstraintsAcyclic : ...
  -- further fields discovered during Phases 1–4
```
Prove that every `Litmus.Test` initial state satisfies `WellFormed` and that `LostPOP t σ σ' → WellFormed σ → WellFormed σ'`. This strengthens results from earlier phases and provides the proof infrastructure for architectural correctness properties.
