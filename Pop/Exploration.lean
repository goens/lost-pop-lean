-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Pop.Litmus
open Std.HashMap
open Util

namespace Pop

variable [Arch]

/-
  Hashing utilities for model-checking deduplication.
  SystemState has no Hashable instance because OrderConstraints wraps Std.HashMap.
  We build a fast fingerprint from the Nat-based fields; collisions fall back to BEq.
-/
private def Request.quickHash (r : Request) : UInt64 :=
  mixHash (hash r.id) $ mixHash (hash r.propagated_to) $
  mixHash (hash r.predecessor_at) $ mixHash (hash r.thread) $
  mixHash (hash r.occurrence) (hash r.pairedRequest?)

private def RequestArray.quickHash (arr : RequestArray) : UInt64 :=
  arr.val.foldl (fun acc opt =>
    mixHash acc (opt.elim 0 Request.quickHash)) 1

private def SystemState.quickHash (state : SystemState) : UInt64 :=
  mixHash state.requests.quickHash $
  mixHash (state.removed.foldl (fun h r => mixHash h (mixHash (hash r.id) (hash r.propagated_to))) 0) $
  state.satisfied.foldl (fun h (r1, r2) => mixHash h (mixHash (hash r1) (hash r2))) 0

-- ProgramState = Array (Array Transition); hash what we can without ArchReq.type
private def ProgramState.quickHash (prog : ProgramState) : UInt64 :=
  prog.foldl (fun acc th =>
    mixHash acc $ th.foldl (fun h tr => mixHash h (match tr with
      | .dependency oid              => hash oid
      | .propagateToThread rid tid   => mixHash (hash rid) (hash tid)
      | .satisfyRead r1 r2           => mixHash (hash r1) (hash r2)
      | .acceptRequest _ tid         => hash tid)) 0) 0

/-- Visited set: HashMap from a cheap hash to a collision-resolution bucket.
    Membership is O(1) amortized vs the previous O(|explored|) linear scan. -/
private abbrev VisitedSet := Std.HashMap UInt64 (Array (ProgramState × SystemState))

private def VisitedSet.contains (visited : VisitedSet) (ps : ProgramState) (ss : SystemState) : Bool :=
  let key := mixHash ps.quickHash ss.quickHash
  match visited.get? key with
  | none        => false
  | some bucket => bucket.any fun (ps', ss') => ps' == ps && ss' == ss

private def VisitedSet.add (visited : VisitedSet) (ps : ProgramState) (ss : SystemState) : VisitedSet :=
  let key := mixHash ps.quickHash ss.quickHash
  match visited.get? key with
  | none        => visited.insert key #[(ps, ss)]
  | some bucket => visited.insert key (bucket.push (ps, ss))

def ProgramState.prettyPrint (accepts : ProgramState) : String :=
  let threadStrings := accepts.map λ th => filterNones $
    th.toList.map Transition.prettyPrintReq
  let allThreads := threadStrings.map λ th => String.intercalate "; " th
  String.intercalate " || " allThreads.toList

def ProgramState.getAvailable (prog : ProgramState) : List (Transition) := Id.run do
  let mut res := []
  for thread in prog do
    if h : thread.size > 0 then
      res := thread[0] :: res
  --dbg_trace "{prog.map λ tr => tr.map Transition.prettyPrintReq}.available = {res.map Transition.prettyPrintReq}"
  return res

def ProgramState.clearDependencies (prog : ProgramState) (state : SystemState)
  : ProgramState := Id.run do
  let mut res := #[]
  let mut thread' := #[]
  for thread in prog do
      thread' := thread
      if let some (Transition.dependency (some req)) := thread[0]? then
        if state.isSatisfied req then
          thread' := thread'.reverse.pop.reverse -- TODO: remove reverses?
      res := res.push thread'
  return res

def ProgramState.consumeTransition (prog : ProgramState) (state : SystemState) (transition : Transition)
  : ProgramState := Id.run do
  unless transition.isAccept do
    return prog
  let mut res : ProgramState := #[]
  let mut thread' := #[]
  let mut found := false -- just consume once
  for thread in prog do
    thread' := thread
    if !found then
      if let some transition' := thread[0]? then
        if transition' == transition then
          thread' := thread'.reverse.pop.reverse -- TODO: somehow don't reverse twice?
          found := true
          -- update dependency
          if let some (Transition.dependency none) := thread'[0]? then
            thread' := thread'.reverse.pop
            thread' := thread'.push (Transition.dependency state.freshId)
                |>.reverse -- TODO: somehow don't reverse twice here either?
    res := res.push thread'
  if found then return res
  else panic! s!"trying to consume non-existing transition: {transition}"

def ProgramState.consumeTrace (prog : ProgramState) (state : SystemState) (trace : List Transition)
: Except String ProgramState := do
  let mut curState := state
  let mut curProg := prog
  for transition in trace do
    let exCurState := state.applyTransition transition
    if let .error e := exCurState then
      throw e
    else
      curState := exCurState.toOption.get!
    curProg := curProg.consumeTransition curState transition |>.clearDependencies curState
  return curProg

-- Should hold: remove · append = id
def ProgramState.appendTransition : ProgramState → Transition → ProgramState
  | prog, trans@(.acceptRequest _ thId) => Id.run do
  let mut res := #[]
  let mut thread' := #[]
  for idx in [:prog.size] do
    thread' := prog[idx]!
    if idx == thId then
      if let some (Transition.dependency (some _)) := thread'[0]? then
        thread' := thread'.reverse.pop -- TODO: another double reverse
        thread' := thread'.push (Transition.dependency none) |>.reverse
      thread' := #[trans] ++ thread'
    res := res.push thread'
  return res
  | prog, _ => prog

def Request.possiblePropagateTransitions (req : Request) (state :  SystemState) : List (Transition) :=
  let threads := state.threads.removeAll req.propagated_to
  --dbg_trace s!"Req {req.id} has not propagated to {threads}"
  let threads_valid := threads.filter (state.canPropagate req.id)
  --dbg_trace s!"Req {req.id} can propagate to {threads_valid}"
  threads_valid.map λ th => Transition.propagateToThread req.id th

def SystemState.possiblePropagateTransitions (state :  SystemState) : List (Transition) :=
  let requests := filterNones state.requests.val.toList
  let requests_not_fully_propagated := requests.filter λ r => ! (@Request.fullyPropagated instArchReq state.scopes r state.scopes.systemScope)
  let removedIds := state.removed.map Request.id
  let requests_active := requests_not_fully_propagated.filter λ r => (state.seen.elem r.id) && (!removedIds.elem r.id)
  -- dbg_trace s!"active requests: {requests_active}"
  List.flatten $ requests_active.map λ r => r.possiblePropagateTransitions state

def Request.possibleSatisfyTransitions (read : Request) (state : SystemState) : List (Transition) :=
  if !read.isRead then [] else
    let requests := filterNones state.requests.val.toList
    let writes_propagated_eq := requests.filter λ write => write.isWrite && write.propagated_to == read.propagated_to
    --dbg_trace s!"writes with eq propagation to {read.id}: {writes_propagated_eq}"
    let write_ids := writes_propagated_eq.map Request.id
    let writes_valid := write_ids.filter (λ write => state.canSatisfyRead read.id write) -- should be length 1
    --dbg_trace s!"valid writes for transition: {writes_valid}"
    writes_valid.map $ Transition.satisfyRead read.id

def SystemState.possibleSatisfyTransitions (state :  SystemState) : List (Transition) :=
  let requests := filterNones state.requests.val.toList
  let unsatisfied_reads := requests.filter λ r => decide (r.isRead ∧ ¬state.isSatisfied r.id)
  List.flatten $ unsatisfied_reads.map λ r => r.possibleSatisfyTransitions state

def SystemState.possibleTransitions (state : SystemState) (unaccepted : ProgramState) :=
  let allaccepts := unaccepted.map λ th => th.filter (λ tr => tr.isAccept || tr.isDependency)
  let accepts := ProgramState.getAvailable allaccepts |>.filter state.canApplyTransition
  accepts ++ state.possibleSatisfyTransitions ++ state.possiblePropagateTransitions

def SystemState.hasUnsatisfiedReads (state : SystemState) :=
  let reads := state.requests.filter (fun r => decide r.isRead) |>.map Request.id
  let unsatisfied := reads.filter λ r => decide (¬state.isSatisfied r)
  unsatisfied != []

def SystemState.isDeadlocked (state : SystemState) (unaccepted : ProgramState) :=
  let transitions := state.possibleTransitions unaccepted
  transitions == [] && state.hasUnsatisfiedReads

-- This should be a monad transformer or smth...
def SystemState.takeNthStep (state : SystemState) (acceptRequests : ProgramState)
(n : Nat) : Except String (Transition × SystemState) :=
  let transitions := state.possibleTransitions acceptRequests
  --dbg_trace s!"possible transitions: {transitions}"
  if transitions.isEmpty then
    throw "No more transitions possible"
  else
    let opTrans := transitions[n.mod transitions.length]?
    match opTrans with
      | none => unreachable!
      | some trans => Except.map (λ st => (trans, st)) (state.applyTransition trans)

def SystemState._runWithList  : SystemState →  ProgramState → List Nat → Except String (SystemState)
  | state, accepts, ns => match ns with
    | [] => throw "Empty transition number list"
    | n::ns =>
      let runStep := state.takeNthStep accepts n
      match runStep with
        | Except.error "No more transitions possible" => Except.ok state
        | Except.ok (trans,state') =>
          -- dbg_trace trans.toString
          -- dbg_trace state'
          let newSt := accepts.consumeTransition state trans |>.clearDependencies state'
          state'._runWithList newSt ns
        | Except.error e => Except.error e

def SystemState.runWithList  : SystemState →  ProgramState → List Nat → Except String (SystemState)
  | state, accepts, ns => if !(List.flatten (accepts.map Array.toList).toList |>.all Transition.isAccept)
  then throw "Running with non-accept transition inputs"
  else SystemState._runWithList state accepts ns

def SystemState.finishedNoDeadlock (state : SystemState) (unaccepted : ProgramState) : Bool :=
  let transitions := state.possibleTransitions unaccepted
  transitions == [] && !state.hasUnsatisfiedReads


def buildInteractiveNumbering : Litmus.Test → List Transition → Option (List Nat)
  | test, transitions => Id.run do
    let mut res := []
    let mut state := test.initState.applyTrace test.initTransitions |>.toOption.get!
    let mut progState := test.program
    for transition in transitions do
      let available := state.possibleTransitions progState
      let idx? := available.findIdx? (λ t => t == transition || (t.isAccept && t.getAcceptBasicRequest? == transition.getAcceptBasicRequest?))
      if let some i := idx? then
        res := res ++ [i]
      else
        panic! s!"cannot find transition ({transition}) in {test.name}; available transitions: {available}"
      let nextSt? := state.applyTransition transition
      if let some nextSt := nextSt?.toOption
        then
          progState := progState.consumeTransition state transition |>.clearDependencies nextSt
          state := nextSt
        else
          panic! s!"error while applying transition {nextSt?}"
    return some (res.map (· + 1))

-- should hold: buildInteractiveNumbering ∘ buildTransitionTrace ≃ Id, buildTransitionTrace ∘ buildInteractiveNumbering ≃ Id
def buildTransitionTrace : Litmus.Test → List Nat → Option (List Transition)
  | test, numTransitions => Id.run do
    let mut res := []
    let mut state := test.initState.applyTrace test.initTransitions |>.toOption.get!
    let mut progState := test.program
    for idx in numTransitions do
      let available := state.possibleTransitions progState
      if let some transition := available[idx - 1]? then
        res := res ++ [transition]
        let nextSt? := state.applyTransition transition
        if let some nextSt := nextSt?.toOption
          then
            progState := progState.consumeTransition state transition
            state := nextSt
          else
            panic! s!"error while applying transition {nextSt?}"
      else
        panic! s!"cannot find transition ({idx}) in available transitions: {available}"
    return some res

def _root_.Litmus.Test.buildTestState : Litmus.Test → List Nat → Except String SystemState
  | test, numTransitions => do
    let initState ← test.initState.applyTrace test.initTransitions
    let opTransitions := buildTransitionTrace test numTransitions
    match opTransitions with
      | some transitions => initState.applyTrace transitions
      | none => Except.error "Invalid trace"

def validTrace : SystemState → ProgramState → List Transition → Bool
  | _, _, [] => true
  | state, prog, trans::rest =>
    let transOk := state.possibleTransitions prog |>.contains trans
    let restOk := match state.applyTransition trans with
      | .error _ => false
      | .ok state' => validTrace state' (prog.consumeTransition state trans) rest
    transOk && restOk

def _root_.Litmus.Test.outcome? (test : Litmus.Test) (trace : List Transition) : Option Litmus.Outcome := test.runTrace trace |>.toOption |>.map SystemState.partialOutcome
def _root_.Litmus.Test.allowed (test : Litmus.Test) : Prop := ∃ trace, validTrace test.initalized test.program trace ∧ test.outcome? trace = some test.expected
def _root_.Litmus.Test.disallowed (test : Litmus.Test) : Prop := ¬ test.allowed

abbrev SearchState := Triple (List Transition) ProgramState SystemState

structure SearchOptions where
 (dontPruneCondition : SystemState → ProgramState → Bool := (λ _ _ => true))
 (stopAfterFirst : Bool := false)
 (storePartialTraces : Bool := true)
 (numWorkers : Nat := 1)
 (singleBatchSize : Nat := 1)
 (multiBatchSize : Nat := 6)
 (breadthFirst : Bool := false)
 (logProgress : Bool := false)
 (maxIterations : Option Nat := none)
 (randomGen : Option StdGen := none)
 (guidingTrace : List Transition := [])

private def searchAuxStep (storePartialTraces : Bool) (partialTrace : List Transition)
(acceptsRemaining : ProgramState) (st : SystemState) : Array SearchState :=
  let transitions := st.possibleTransitions acceptsRemaining
  transitions.toArray.map λ t =>
    let newPT := (if storePartialTraces
                  then partialTrace ++ [t]
                  else [])
    -- TODO: add potential to sanity check
    let newST := st.applyTransition! t
    let newAC :=  acceptsRemaining.consumeTransition st t |>.clearDependencies newST
    (newPT,newAC,newST)t

private def searchAuxUpdateUnexplored (explored unexplored newtriples : Array SearchState) : Array SearchState :=
  let filterFun := λ (_,newProgState,newSysState)t =>
    let checkFun := λ (_,progState,sysState)t =>
      newProgState != progState || newSysState != sysState
    (unexplored.all checkFun && explored.all checkFun)
  Array.append (newtriples.filter filterFun) unexplored

/-- Filter newtriples to those not already in the visited set (covers both explored
    and in-queue states). O(|newtriples|) amortized instead of
    O(|newtriples| × (|explored| + |unexplored|)). -/
private def searchAuxUpdateUnexploredVisited
    (visited : VisitedSet) (unexplored newtriples : Array SearchState) : Array SearchState × VisitedSet :=
  let filtered := newtriples.filter λ (_,ps,ss)t =>
    !visited.contains ps ss
  let vis' := filtered.foldl (fun v (_,ps,ss)t => v.add ps ss) visited
  (Array.append filtered unexplored, vis')


private def searchAuxNSteps (options : SearchOptions) (inputStates : Array SearchState)
 : (List ((List Transition) × SystemState)) × Array SearchState := Id.run do
 let mut unexplored := inputStates
 let mut stepsRemaining := options.singleBatchSize
 let mut found := []
 let stepFun := searchAuxStep options.storePartialTraces
 while h : unexplored.size > 0 && stepsRemaining > 0 do
   let (partialTrace,acceptsRemaining,st)t := unexplored[unexplored.size - 1]'
     (by rw [Bool.and_eq_true] at h
         let h' := of_decide_eq_true $ And.left h
         exact n_minus_one_le_n h')
   let newTriplesRaw := stepFun partialTrace acceptsRemaining st
   let newTriples := newTriplesRaw.filter λ (_,ps,ss)t =>
     options.dontPruneCondition ss ps
   unexplored := unexplored.pop
   unexplored := searchAuxUpdateUnexplored #[] unexplored newTriples
   --dbg_trace "popped {partialTrace}, remaining unexplored{unexplored.map λ (pt,_,_)t => pt} "
   stepsRemaining := stepsRemaining - 1
   found := List.append found $ filterNones $ unexplored.toList.map λ (pt,ps,ss)t =>
     if ss.finishedNoDeadlock ps
     then some (pt,ss)
     else none
   if options.stopAfterFirst && found.length > 0
     then return (found,unexplored)
   --dbg_trace "returning unexplored: {unexplored.map λ triple => triple.1}"
 (found,unexplored)

-- the unapologetically imperative version:
def SystemState.exhaustiveSearch (state : SystemState) (inittuple : (List (Transition)) × ProgramState)
  (options : SearchOptions) : Except String $ List ((List Transition) × SystemState) :=
match inittuple with
  | (inittransitions, accepts) =>
  let stateinit := state.applyTrace inittransitions
  let stepFun := searchAuxNSteps options
  match stateinit with
    | .ok startState =>
    Id.run do
      -- either save the state (memory cost) or recompute it (computational cost)
      -- we choose the former so that we can also filter out states that we've seen before
      let mut unexplored := #[([],accepts,startState)t]
      -- visited covers both explored and in-queue states: O(1) amortized deduplication
      -- vs the previous O(|unexplored|) linear scan on every new triple
      let mut visited : VisitedSet := (({} : VisitedSet).add accepts startState)
      let mut visited_size : Nat := 0
      let mut found : Array ((List Transition) × SystemState) := #[]
      let mut cur_size := 0
      let mut randGen := options.randomGen
      let mut guide := options.guidingTrace
      let mut thousands_explored : UInt32 := 1
      --dbg_trace s!"litmus: {accepts.prettyPrint}"
      --dbg_trace s!"starting state:\n{startState}"
      let mut workers : Array (Task ((List ((List Transition) × SystemState)) × (Array SearchState))) := #[]
      while unexplored.size > 0 do
          --dbg_trace s!"{unexplored.size} unexplored"
          let n := min unexplored.size (max options.numWorkers 1) -- at least 1
          for i in [0:n] do
            let mut idx := if options.breadthFirst then unexplored.size - 1 else i
            if let some g := randGen then
              let (n,g') := RandomGen.next g
              randGen := some g'
              if n % 5 == 0 then -- 20%
                idx := (idx + n) % unexplored.size
            if let transition::rest := guide then
              unless unexplored[0]!.fst.isEmpty do
                let (first,last) := unexplored.partition
                  λ (pt,_,_)t => pt.getLast? == some transition
                let firstSorted := first.qsort λ (pt,_,_)t (pt',_,_)t => Nat.ble pt'.length pt.length -- longest first!
                unexplored := firstSorted ++ last
                if !firstSorted.isEmpty then -- don't consume transition unless actually found something
                  guide := rest
                idx := 0
            let some unexplored_cur := unexplored[idx]?
              | panic! "index error, this shouldn't happen" -- TODO: prove i is fine
            -- Swap-erase: O(1) instead of O(n) eraseIdx for DFS (idx near front)
            if idx < unexplored.size - 1 then
              unexplored := unexplored.set! idx unexplored.back!
            unexplored := unexplored.pop
            visited_size := visited_size + 1
            let task := Task.spawn λ _ => stepFun #[unexplored_cur]
            workers := workers.push task
          for worker in workers do
            let (newFound,newTriples) := worker.get
            found := found.append newFound.toArray
            if options.stopAfterFirst && found.size > 0 then
              unexplored := #[]
              break
            if let some n := options.maxIterations then
              if visited_size > n then
                return Except.error s!"Exceeded max. number of iterations({n})"
            if options.logProgress then
              if newTriples.any λ (pt,_,_)t => pt.length > cur_size then
                cur_size := cur_size + 1
                dbg_trace "progress: partial traces of size {cur_size}"
              if visited_size.toUInt32 > thousands_explored  * 1000 then
                dbg_trace "progress: explored ≥{thousands_explored}k"
                thousands_explored := thousands_explored + 1

            let (newUnexplored, newVisited) := searchAuxUpdateUnexploredVisited visited unexplored newTriples
            unexplored := newUnexplored
            visited := newVisited
            if options.stopAfterFirst && found.size > 0 then
              break
            --dbg_trace "total unexplored: {unexplored.size}"
          workers := #[]
      return Except.ok found.toList
    | .error e => .error e

def SystemState.exhaustiveSearchLitmus
  (state : SystemState) (litmus : (List Transition) × ProgramState × Litmus.Outcome) (options : SearchOptions)
  : Except String $ List ((List Transition) × SystemState) :=
    let (inittrans,progstate,expectedOutcome) := litmus
    let pruneFun := λ ss _ => ss.outcomePossible expectedOutcome progstate
    state.exhaustiveSearch (inittrans,progstate) {options with dontPruneCondition := pruneFun}


def _root_.Litmus.Test.exhaustiveSearch (test : Litmus.Test) (stopAfterFirst : optParam Bool false)
  (storePartialTraces : optParam Bool true) (numWorkers : optParam Nat 7)
  (batchSize : optParam Nat 15) (breadthFirst : optParam Bool false)
  (logProgress : optParam Bool false) (maxIterations : optParam (Option Nat) none) :
  Except String $ List ((List Transition) × SystemState) :=
    let options : SearchOptions := { stopAfterFirst, storePartialTraces, numWorkers, singleBatchSize := batchSize, breadthFirst, logProgress, maxIterations}
  test.initState.exhaustiveSearchLitmus (test.initTransitions,test.program,test.expected) options

def runMultipleLitmusAux (tests : List Litmus.Test) (options : SearchOptions)
  : List ((Litmus.Test) × (Except String $ (List Litmus.Outcome) × (List ((List Transition) × SystemState)))) := Id.run do
    let mut tasks  := #[]
    for test@(Litmus.Test.mk initTrans initProg outcome _ startingState _ _ guides) in tests do
      let task := Task.spawn λ _ =>
        let guide := match guides.head? with
          | some trace => trace
          | none => []
        let resExplExcept := startingState.exhaustiveSearchLitmus (initTrans,initProg,outcome) {{options with stopAfterFirst := true} with guidingTrace := guide}
        match resExplExcept with
          | .ok resExpl =>
             let resLitmus := Util.removeDuplicates $ resExpl.map λ (_,st) => st.partialOutcome
             let pts := Util.removeDuplicates $ resExpl
             (test, Except.ok (resLitmus, pts))
          | .error e => (test, Except.error e)
      tasks := tasks.push task
    return tasks.map Task.get  |>.toList

def runMultipleLitmus (tests : List Litmus.Test) (logProgress := false) (batchSize := 6) (maxIterations := some 20000) (randomSeed : optParam (Option Nat) none)
: List ((Litmus.Test) × (Except String $ (List Litmus.Outcome) × (List ((List Transition) × SystemState))))
  := Id.run do
    let randomGen := match randomSeed with | none => none | some n => some $ mkStdGen n
    let options : SearchOptions := {logProgress, multiBatchSize := batchSize, maxIterations, randomGen}
    let mut res := []
    let mut remaining := tests
    while !remaining.isEmpty do
      let testBatch := remaining.take batchSize
      remaining := remaining.drop batchSize
      res := res ++ (runMultipleLitmusAux testBatch options)
    return res

def prettyPrintLitmusResult : Litmus.Test → (Except String $ (List Litmus.Outcome) × (List ((List Transition) × SystemState))) →
(printWitness : optParam Bool true) → (printHead : optParam Bool true) → (nameColWidth : optParam Nat 30) → String
  | test, resExcept , printWitness, printHead, nameColWidth =>
     --  (reslit, pts)
     let outcome_res := match resExcept with
       | .error _ => "𐄂?"
       | .ok (reslit,_) => if reslit.any λ out => outcomeEquiv out test.expected
         then "✓"
         else "𐄂"
     let (pt, opState) := match resExcept with
       | .error _ => ([], none)
       | .ok (_, pts) =>
         let pts_outcome := pts.filter
             λ ptTup => outcomeEquiv test.expected (SystemState.partialOutcome (Prod.snd ptTup))
         match pts_outcome.head? with
         | some pt => (pt.1, some pt.2)
         | none => ([], none)
     let ptString := match opState with
       | none => ""
       | some _ => toString $ pt.map Transition.toString
     let axiomatic := test.axiomaticAllowed.toString
     let ptNums := buildInteractiveNumbering test pt
     let outcomeStr := if outcome_res == "𐄂?" then outcome_res else (outcome_res ++ " ")
     let uncolored := s!"| {test.name}" ++ (String.ofList $ List.replicate (nameColWidth - test.name.length - 3) ' ') ++
                   s!"| {axiomatic}         | {outcomeStr}  |"
     let resStr := if axiomatic != "?" && outcome_res != "𐄂?" && axiomatic != outcome_res
       then colorString .red uncolored
       else if (outcome_res == "𐄂?" && axiomatic == "𐄂" || axiomatic == "?")
       then colorString .cyan uncolored
       else if outcome_res == "𐄂?" && axiomatic == "✓"
       then colorString .yellow uncolored
       else uncolored
     let witnessStr := if outcome_res == "✓" && printWitness && ptNums.isSome
       then s!"\n    Witness: {ptNums.get!} →\n hint for {test.name} := {ptString}\n"
       else ""
     let headStr := if printHead
     then
       let testTitleRaw := "| Litmus test "
       let testTitle := testTitleRaw ++ (String.ofList $ List.replicate (nameColWidth - testTitleRaw.length - 1) ' ')
       s!"{testTitle}| Axiomatic | POP |\n" ++ (String.ofList $ List.replicate (nameColWidth + 18) '-') ++ "\n"
     else ""
     headStr ++ resStr ++ witnessStr

def printMultipleLitmusResults : List (Litmus.Test × (Except String $ List Litmus.Outcome × List (List Transition × SystemState))) → (printWitnesses : optParam Bool false) → String
  | results, printWitnesses => Id.run do
  let mut first := true
  let mut resStr := ""
  let colLength := match List.max? $ results.map λ (t,_) => t.name.length with
    | none => 40
    | some l => l + 5
  for (test,res) in results do
    resStr := resStr ++ (prettyPrintLitmusResult test res (printWitness := printWitnesses) (printHead := first) (colLength)) ++ "\n"
    first := false
  return resStr

/-
  Id.run do
    let mut res := ""
    let mut curThread : ThreadId := 0
    for (thread, addr, opval) in outcome do
      while (ThreadId.toNat curThread ) < (ThreadId.toNat thread) do
        -- assumes lexBLe, won't add multiple ||'s
        res := res ++ "|| "
        curThread := (ThreadId.toNat curThread) + 1
      let some val := opval then
        res := res ++ s!"x{addr} := {val}; "
      else
        res := "invalid outcome!"
        break
    return res
    -/
-- | state, accepts => state.runDFS accepts λ _ => false

    -- let runStep := λ (acceptsRemaining, state) n => state.takeNthStep acceptsRemaining n
    -- ns.foldlM (init := (accepts, state)) runStep
    -- ns.foldlM  (init := state) λ state.takeNthStep accepts.zip ns
