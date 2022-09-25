import Pop.Litmus
import Pop.Exploration
import Pop.Util

-- For now specifically for PTX
import Pop.Arch.PTX

open Pop

-- TODO: should we do this arch-generic?
    -- variable [Arch]


def toSizes (litmus : Litmus.Test) : String :=
  let usedScopes := Util.filterNones $ List.join $
    (List.range litmus.program.size).map
      λ thId => litmus.program[thId]!.toList.map
        λ transition =>
          match transition.getAcceptBasicRequest? with
            | none => none
            | some br => some $ PTX.getThreadScope
                litmus.initState.scopes thId br.type.scope |>.threads
  s!"  # ptx/Thread = {litmus.initState.threads.length}\n" ++
  s!"  # ptx/Read = {litmus.program.allReads.length}\n" ++
  s!"  # ptx/Write = {litmus.program.allWrites.length}\n" ++
  s!"  # ptx/Fence = {litmus.program.allBarriers.length}\n" ++
  s!"  # ptx/Barrier = 0\n" ++ -- Not considering these for now
  -- Add the number of threads to scopes, as we don't consider them to be scopes
  s!"  # ptx/Scope = {usedScopes.uniqueSet.length + litmus.program.size}\n"

def transToAlloy : Transition → String
  | .acceptRequest br _ =>
  match br with
    | .read _ ty =>
      match ty.sem with
        | .acq => "ptx/Acquire"
        | _ => "ptx/Read - ptx/Acquire"
    | .write _ ty =>
      match ty.sem with
        | .rel => "ptx/Release"
        | _ => "ptx/Write - ptx/Release"
    | .barrier ty =>
      match ty.sem with
        | .sc => "ptx/FenceSC"
        | .acqrel => "ptx/FenceAcqRel"
        | .rel => "ptx/FenceRel"
        | .acq => "ptx/FenceAcq"
        | _ => "ptx/Fence"
  | _ => "UNKNOWN_TRANSITION"

def toPreds (litmus : Litmus.Test) : String :=
  let threads := String.intercalate ",\n    " $ litmus.initState.threads.map λ th => s!"t{th} : ptx/Thread"
  let readTransitions := litmus.program.allReads
  let readNames := readTransitions.zip (List.range readTransitions.length) |>.map
    λ (r,i) => (r,s!"r{i}")
  let writeTransitions := litmus.program.allWrites
  let writeNames := writeTransitions.zip (List.range writeTransitions.length) |>.map
    λ (w,i) => (w,s!"w{i}")
  let fenceTransitions := litmus.program.allBarriers
  let fenceNames := fenceTransitions.zip (List.range fenceTransitions.length) |>.map
    λ (f,i) => (f,s!"f{i}")
  let transitions := readTransitions ++ writeTransitions ++ fenceTransitions
  let transitionNames := readNames ++ writeNames ++ fenceNames
  let names := String.append (threads ++ ",\n    ") $
    String.intercalate ",\n    " $ transitionNames.map
      λ (t,name) => s!"{name} : {transToAlloy t}"

  -- Generate PO predicates
  let po := Id.run do
    let mut res := ""
    let mut opLast := none
    let mut thId := 0
    for thread in litmus.program do
      for transition in thread do
        if opLast.isNone then -- the first transition in a thread
          opLast := transitionNames.lookup? transition
          res := res ++ s!"    t{thId}.start = {opLast.get!} and\n"
          continue
        if let (some cur, some last) := (transitionNames.lookup? transition, opLast) then
          res := res ++ s!"    {last}.po = {cur} and\n"
        opLast := transitionNames.lookup? transition -- second transition onward
      -- end thread iteration: update state
      thId := thId + 1
      opLast := none
    return res

  let memops := litmus.program.allReads ++ litmus.program.allWrites
  -- Generate address predicates
  let addresses := Id.run do
    let mut res := ""
    let mut address_groups : List (Address × String) := []
    for transition in memops do
      let some br := transition.getAcceptBasicRequest?
        | panic! s!"cannot get basic request from {transition}"
      let some address := br.address?
        | panic! s!"Unknown address in {br}"
      let some transName := transitionNames.lookup? transition
        | panic! s!"Unknown transition {transition}"
      if let some refAddress := address_groups.lookup? address
        -- Not first time seen: then they should be equal
        then res := res ++ s!"    {refAddress}.address = {transName}.address and\n"
        -- First transition with this address: add as reference value
        else address_groups := (address, transName) :: address_groups
    -- Finally: the reference addresses should be pairwise different
    for (_,name₁) in address_groups do
      for (_,name₂) in address_groups do
        if name₁ != name₂ then
          res := res ++ s!"    {name₁}.address != {name₂}.address and\n"
        else break -- do not add symmetric constraints
    return res
  let scopes := Id.run do
    let mut res := ""
    for thId in (List.range litmus.program.size) do
      for transition in litmus.program[thId]! do
        let some br := transition.getAcceptBasicRequest?
          | panic! s!"invalid transition {transition}"
        let some transName := transitionNames.lookup? transition
          | panic! s!"Unknown transition {transition}"
        -- Handle special case for system scope (less verbose)
        if br.type.scope == PTX.Scope.sys then
          res := res ++ s!"    {transName}.scope = System and\n"
          continue
        let scope : Scope := PTX.getThreadScope litmus.initState.scopes thId br.type.scope
        for thread in (List.range litmus.program.size) do
          let contains := if scope.threads.contains thread
            then ""
            else "not "
          res := res ++ s!"    t{thread} {contains}in {transName}.scope.*subscope and\n"
    return res
  let outcome := Id.run do
    let mut res := ""
    let rfPairs := litmus.expected.toRFPairs litmus.program
    for (read,opWrite) in rfPairs do
      let some readName := transitionNames.lookup? read
        | panic! s!"invalid write ({read}) in outcome"
      if let some write := opWrite then
       -- The read has a corresponding write (rf)
        let some writeName := transitionNames.lookup? write
          | panic! s!"invalid write ({write}) in outcome"
        res := res ++ s!"    {writeName}.rf = {readName} and\n"
      else
       -- The read has no corresponding (rf) write
        res := res ++ s!"    no {readName}.~rf and\n"
    return res

  s!"\n  some\n    {names} |\n" ++
  s!"\n    // Program Order\n{po}\n" ++
  s!"    // Addresses \n{addresses}\n" ++
  s!"    // Scopes \n{scopes}\n" ++
  s!"    // Outcome \n{outcome}\n" ++
  s!"  ptx_mm\n\n"


def toAlloyLitmus (litmus : Litmus.Test ) : String :=
  "module litmus\n" ++
  "open ptx as ptx\n" ++
  "pred generated_litmus_test {\n" ++
  s!"{toSizes litmus}" ++
  s!"{toPreds litmus}" ++
  "}\n" ++ "run generated_litmus_test for 10"


#eval toAlloyLitmus PTX.Litmus.IRIW
