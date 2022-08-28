import Pop.Litmus
import Pop.Exploration

-- For now specifically for PTX
import Pop.Arch.PTX

open Pop

-- TODO: should we do this arch-generic?
    -- variable [Arch]


def toSizes (litmus : Litmus.Test) : String :=
  s!"  # ptx/Thread = {litmus.initState.threads.length}\n" ++
  s!"  # ptx/Read = {litmus.program.allReads.length}\n" ++
  s!"  # ptx/Write = {litmus.program.allWrites.length}\n" ++
  s!"  # ptx/Fence = {litmus.program.allBarriers.length}\n"

def transToAlloy : Transition → String
  | .acceptRequest br _ =>
  match br with
    | .read _ ty =>
      match ty.sem with
        | .acq => "ptx/Acquire"
        | _ => "ptx/Read"
    | .write _ ty =>
      match ty.sem with
        | .rel => "ptx/Release"
        | _ => "ptx/Write"
    | .barrier ty =>
      match ty.sem with
        | .sc => "ptx/FenceSC"
        | .acqrel => "ptx/FenceAcqRel"
        | .rel => "ptx/FenceRel"
        | .acq => "ptx/FenceAcq"
        | _ => "ptx/Fence"
  | _ => "UNKNOWN_TRANSITION"

def toPreds (litmus : Litmus.Test) : String :=
  -- let reads := 
  -- let writes := 
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
  let transitionNames := readNames ++ writeNames ++ fenceNames
  let names := String.append (threads ++ ",\n    ") $
    String.intercalate ",\n    " $ transitionNames.map
      λ (t,name) => s!"{name} : {transToAlloy t}"
  let po := Id.run do
    let mut res := ""
    let mut opLast := none
    let mut thId := 0
    for thread in litmus.program do
      for transition in thread do
        if opLast.isNone then
          opLast := transitionNames.lookup? transition
          res := res ++ s!"    t{thId}.start = {opLast.get!},\n"
          continue
        opLast := transitionNames.lookup? transition
        if let (some cur, some last) := (transitionNames.lookup? transition, opLast) then
          res := res ++ s!"    {last}.po = {cur},\n"
      thId := thId + 1
      opLast := none
    return res
  let addresses := ""
  let scopes := ""
  let outcome := ""
  s!"\n  some\n    {names} |\n" ++
  s!"\n    // Program Order\n{po}\n" ++
  s!"    // Addresses \n{addresses}\n" ++
  s!"    // Scopes \n{scopes}\n" ++
  s!"    // Outcome \n{outcome}\n"


def toAlloyLitmus (litmus : Litmus.Test ) : String :=
  "module litmus\n" ++
  "open ptx as ptx\n" ++
  "pred generated_litmus_test {\n" ++
  s!"{toSizes litmus}" ++
  s!"{toPreds litmus}" ++
  "}\n" ++ "run generated_litmus_test for 10"


#eval toAlloyLitmus PTX.Litmus.IRIW

