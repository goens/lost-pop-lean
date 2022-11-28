import Pop.Util
import Pop.Pop
import Pop.States
import Lean
import Pop.Util

open Std.HashMap
open Util

namespace Litmus
open Util Pop Lean

variable [Arch]

structure ReadOutcome where
  thread : ThreadId
  address : Address
  value : Value
  occurrence : Nat
  deriving BEq, Inhabited

def ReadOutcome.toString (out : ReadOutcome) : String := s!"{out.occurrence}-th read {out.address} at thread {out.thread} with value {out.value}"
instance : ToString ReadOutcome where toString := ReadOutcome.toString

abbrev Outcome := List ReadOutcome

inductive AxiomaticAllowed
  | yes
  | no
  | unknown
  deriving BEq

def AxiomaticAllowed.toString : AxiomaticAllowed → String
  | yes => "✓"
  | no => "𐄂"
  | unknown => "?"

instance : ToString AxiomaticAllowed where toString := AxiomaticAllowed.toString

structure Test where
 (initTransitions : List Transition)
 (program : ProgramState)
 (expected : Outcome)
 (initState : SystemState)
 (name : String)
 (axiomaticAllowed : AxiomaticAllowed)
 (guideTraces : List $ List Transition)

def Test.numThreads (test : Test) : Nat := test.program.size
def Test.numInstructions (test : Test) : Nat := Array.sum $ test.program.map (λ th => th.size)
def Test.numScopes (test : Test)  : Nat := test.initState.scopes.scopes.toList.length
def Test.weightedSize (test : Test)  : Nat := test.numThreads * 100 + test.numInstructions * 10 + test.numScopes

end Litmus

namespace Pop
variable [Arch]
def SystemState.partialOutcome : SystemState → Litmus.Outcome
| state =>
  let reqToReadOutcome := λ rd : Request =>
    { thread := rd.thread, address := rd.address?.get!, value := rd.value?,
      occurrence := rd.occurrence : Litmus.ReadOutcome}
  let removed : List Litmus.ReadOutcome := state.removed.map reqToReadOutcome
  let satisfied := state.requests.filter Request.isSatisfied |>.map reqToReadOutcome
  removed ++ satisfied

def outcomeSubset : Litmus.Outcome → Litmus.Outcome → Bool
  | out₁, out₂ =>
  out₁.all λ readOutcome => out₂.contains readOutcome

def outcomeEquiv : Litmus.Outcome → Litmus.Outcome → Bool
  | out₁, out₂ => outcomeSubset out₁ out₂ && outcomeSubset out₂ out₁

def SystemState.outcomePossible : Litmus.Outcome → ProgramState → SystemState → Bool
 | expectedOutcome, program, state => Id.run do
   -- Commented out: this pruning should be better/stronger, but it seems to make things slower and/or be wrong
   -- let rfpairs := expectedOutcome.toRFPairs program
   -- for ((readTrans,readNum),opWrite) in rfpairs do
   --   if let some (writeTrans,writeNum) := opWrite then
   --     if let some read := readTrans.getAcceptBasicRequest? then
   --       if let some write := writeTrans.getAcceptBasicRequest? then
   --         let stWrites := state.requests.filter
   --           λ req => req.address? == write.address? && some req.thread == writeTrans.thread?
   --             && req.occurrence == writeNum && write.value? == req.value?
   --         let stReads := state.requests.filter
   --           λ req => req.address? == read.address? && some req.thread == readTrans.thread?
   --             && req.occurrence == readNum
   --         if let (some stRead, some stWrite) := (stReads[0]?, stWrites[0]?) then
   --           let scope := state.scopes.jointScope stRead.thread stWrite.thread
   --           if state.orderConstraints.lookup scope stWrite.id stRead.id then
   --             return false
   -- if nothing breaks from
   return outcomeSubset state.partialOutcome expectedOutcome

end Pop

namespace Litmus
open Util Pop Lean

variable [Arch]

def Test.trace (test : Test) (trace : List Transition) : Except String SystemState := test.initState.applyTrace (test.initTransitions ++ test.program.all ++ trace)
def Test.outcome? (test : Test) (trace : List Transition) : Option Outcome := test.trace trace |>.toOption |>.map SystemState.partialOutcome
def Test.allowed (test : Test) : Prop := ∃ trace, test.outcome? trace = some test.expected
def Test.disallowed (test : Test) : Prop := ¬ test.allowed

instance : Inhabited Test where default := { initTransitions := [], program := #[], expected := [], initState := default, name := "default", axiomaticAllowed := .unknown, guideTraces := []}

def addressValuePretty : Address × Value → String
  | (_, none) => "invalid outcome!"
  | (addr, some val) => s!"{addr.prettyPrint} = {val}"

def Outcome.prettyPrint : Litmus.Outcome → String
  | outcome =>
  let threads : List Litmus.Outcome := outcome.groupBy (·.thread == ·.thread)
    |>.toArray.qsort (λ t₁ t₂ => Nat.ble t₁.head!.thread t₂.head!.thread) |>.toList
  let threadStrings := threads.map
    λ th => String.intercalate "; " $ th.map (λ readOut => addressValuePretty $ (readOut.address, readOut.value))
  String.intercalate " || " threadStrings


-- Assumes each value written at most once per address!
def simpleOutcomeToRFPairs (outcome :  List $ ThreadId × Address × Value) (prog : ProgramState)
  : List ((Transition × Nat) × Option (Transition × Nat)) := Id.run do
  let mut res : List ((Transition × Nat) × Option (Transition × Nat)) := []
  -- First we bulid a map of values to the respective writes
  let mut value_map : List ((Value × Address) × (Transition × Nat)) := []
  for (writeTrans,num) in prog.allWrites.countOcurrences do
    let some write := writeTrans.getAcceptBasicRequest?
      | panic! s!"invalid write {writeTrans}"
    let pair := (write.value?, write.address?.get!)
    value_map := (pair, (writeTrans,num)) :: value_map
  -- Now add the predicates for the outcome
  let mut seenTrans : List ((ThreadId × Transition) × Nat) := []
  for (thId, addr, value) in outcome do
    for readTrans in prog[thId.toNat]! do
      unless readTrans.isReadAccept do
        continue
      let num := match seenTrans.lookup (thId,readTrans) with
        | none => 1
        | some n => n + 1
      seenTrans := ((thId,readTrans), num) :: seenTrans
      let some read := readTrans.getAcceptBasicRequest?
        | panic! s!"invalid read {readTrans}"
      unless some addr == read.address? do
        continue
      -- Thread and address match (because of the guard above +
      -- iterating only in that thread). We can add it to the list.
      let pair := (value, addr)
      if let some writeTransNum := value_map.lookup pair
        then res := ((readTrans, num),some writeTransNum) :: res
        else res := ((readTrans, num), none) :: res
      break
  return res

def Outcome.toRFPairs (outcome : Outcome) (prog : ProgramState)
  : List $ (Transition × Nat) × Option (Transition × Nat) :=
   let simple := outcome.map λ r => (r.thread,r.address,r.value)
   simpleOutcomeToRFPairs simple prog

declare_syntax_cat request
declare_syntax_cat request_seq
declare_syntax_cat request_set
declare_syntax_cat threads
declare_syntax_cat system_desc
declare_syntax_cat metadata_item
declare_syntax_cat litmus_metadata
declare_syntax_cat litmus_def
declare_syntax_cat guide_trace (behavior := both)
declare_syntax_cat transition (behavior := both)

syntax "R" ident ("//" num)? : request
syntax "RMW" ident ("//" num)? : request
syntax "R." ident ident  ("//" num)? : request
syntax "W" ident "=" num : request
syntax "W." ident ident "=" num : request
syntax "Fence"   : request
syntax "Fence." ident  : request
syntax request ";" request_seq : request_seq
syntax request ";dep" request_seq : request_seq
syntax request : request_seq
syntax request_seq "||" request_set : request_set
syntax request_seq : request_set
syntax ident,+ : threads
syntax "{" threads "}" : system_desc
syntax "{" threads "}." ident : system_desc
syntax "{" system_desc,+ "}" : system_desc

syntax "✓" : metadata_item
syntax "𐄂" : metadata_item
syntax &"Accept" "(" request ")" " at " &"Thread " num : transition
syntax &"Propagate " &"Request " num " to " &"Thread " num : transition
syntax &"Satisfy " &"Request " num " with " &"Request " num : transition
syntax "[" transition,+ "]" : guide_trace
syntax metadata_item (litmus_metadata)? : litmus_metadata

syntax "{|" request_set "|}" ("where" "sys" ":=" system_desc )? (litmus_metadata)? : litmus_def
syntax "`[litmus|" litmus_def ident "]" : term
syntax "`[sys|" system_desc "]" : term
syntax "`[req|" request "]" : term
syntax "`[req_seq|" request_seq "]" : term
syntax "`[req_set|" request_set "]" : term
syntax "`[metadata|" ident "|" litmus_metadata "]" : term
syntax "`[guide_trace|" guide_trace "]" : term
syntax "`[transition|" transition "]" : term


-- Define an attribute to add up all Litmus tests
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Stateful.2FAggregating.20Macros.3F/near/301067121
abbrev NameExt := SimplePersistentEnvExtension (Name × Name) (NameMap Name)

private def mkExt (name attr : Name) (descr : String) : IO NameExt := do
  let addEntryFn | m, (n3, n4) => m.insert n3 n4
  let ext ← registerSimplePersistentEnvExtension {
    name, addEntryFn
    addImportedFn := mkStateFromImportedEntries addEntryFn {}
  }
  registerBuiltinAttribute {
    name := attr
    descr
    add := fun declName stx attrKind => do
      let s := ext.getState (← getEnv)
      let ns ← stx[1].getArgs.mapM fun stx => do
        let n := stx.getId
        if s.contains n then throwErrorAt stx "litmus test {n} already declared"
        pure n
      modifyEnv $ ns.foldl fun env n =>
        ext.addEntry env (n, declName)
  }
  pure ext


private def mkElab (ext : NameExt) (ty : Lean.Expr) : Elab.Term.TermElabM Lean.Expr := do
  let mut stx := #[]
  for (_, n4) in ext.getState (← getEnv) do
    stx := stx.push $ ← `($(mkIdent n4):ident)
  let listStx := (← `([$stx,*]))
  let sorted ← `(Array.toList $ Array.qsort ($listStx).toArray (λ x y => Nat.ble x.weightedSize y.weightedSize))
  Elab.Term.elabTerm sorted (some ty)

syntax (name := litmusTest) "litmusTest " ident+ : attr
initialize litmusExtension : NameExt ←
  mkExt `Pop.litmusExtension `litmusTest
    (descr := "Litums Tests")

elab "litmusTests!" : term <= ty => do
  mkElab litmusExtension ty

macro "deflitmus" name:ident " := " litmus:litmus_def : command => do
  let litmus_term ← `(`[litmus| $litmus $name])
  `(@[litmusTest $name] def $name := $litmus_term)

syntax (name := litmusHint) "litmusHint " ident+ : attr
initialize litmusHintExtension : NameExt ←
  mkExt `Pop.litmusHintExtension `litmusHint
    (descr := "Litums Trace Hints Tests")

private def mkHintElab (ext : NameExt) (litmus : Name) (ty : Lean.Expr) : Elab.Term.TermElabM Lean.Expr := do
  let mut stx := #[]
  for (nm, n4) in ext.getState (← getEnv) do
    if nm == litmus then
      stx := stx.push $ ← `($(mkIdent n4):ident)
  let listStx := (← `([$stx,*]))
  Elab.Term.elabTerm listStx (some ty)

macro "hint " "for " name:ident " := " g:guide_trace : command => do
  let newName := Name.str .anonymous $ name.getId.toString ++ "_hint"
  `(@[litmusHint $name] def $(mkIdent newName) := `[guide_trace| $g])

elab "litmusHints!" name:ident : term <= ty => do
  mkHintElab litmusHintExtension name.getId ty


end Litmus

namespace Pop
open Lean

variable [Arch]

class LitmusSyntax where
  mkRead : String → Address → String → BasicRequest
  mkRMW : String → Address → String → BasicRequest × BasicRequest
  mkWrite : String → Address → Value → String → BasicRequest
  mkFence : String → String → BasicRequest
  (toAlloy :  String → BasicRequest → String := λ _ _ => "UNKNOWN_REQUEST")
  (alloyName :  String := "???")

def mkValidScopes (n : Nat) : ValidScopes :=
  { system_scope := List.range n, scopes := ListTree.leaf (List.range n)}

variable [LitmusSyntax]
open LitmusSyntax

def mkRequest : String × String × Address × Value → ThreadId → String → List Transition
  | ("R", typeStr, addr, _), thId, thTy => [Pop.Transition.acceptRequest (mkRead typeStr addr thTy) thId]
  | ("RMW", typeStr, addr, _), thId, thTy => [Pop.Transition.acceptRequest (mkRead typeStr addr thTy) thId,  Pop.Transition.acceptRequest (mkRead typeStr addr thTy) thId]
  | ("W",typeStr , addr, val), thId, thTy  => [Pop.Transition.acceptRequest (mkWrite typeStr addr val thTy) thId]
  | ("Fence", typeStr, _, _), thId, thTy => [Pop.Transition.acceptRequest (mkFence typeStr thTy) thId]
  | ("Dependency", _, _, _), thId, thTy => [Pop.Transition.acceptRequest (mkFence "sys_dep" thTy) thId] -- hack: sys_dep
  -- | ("Dependency", _, _, _), _, _ => some $ Pop.Transition.dependency none
  | _, _, _ => []

def mkReadOutcomeTriple : String × String × Address × Value → ThreadId → Option (ThreadId × Address × Value)
  | ("R", _, addr, val@(some _)), thId  => some (thId,addr,val)
  | _, _ => none

def mkOutcome : List (ThreadId × Address × Value) → Litmus.Outcome
  | readOutcomes =>
    let (th_addr_pairs, vals) := readOutcomes.map (λ (th, addr, val) => ((th,addr),val)) |>.unzip
    th_addr_pairs.countOcurrences.zip vals |>.map
    λ (((thId,addr),num),val) =>
      { thread := thId, address := addr, value := val, occurrence := num}

def initZeroesUnpropagatedTransitions : String → List Address → List (Transition)
  | threadType, addresses =>
  -- Does the threadId matter? For now, using 0
  addresses.map λ addr => Pop.Transition.acceptRequest (mkWrite "" addr 0 threadType) 0

def SystemState.initZeroesUnpropagated! : SystemState → List Address → SystemState
  | state, addresses =>
    let writeReqs := initZeroesUnpropagatedTransitions (state.threadTypes 0) addresses
    state.applyTrace! writeReqs

def SystemState.initZeroesUnpropagated : SystemState → List Address → Except String (SystemState)
  | state, addresses =>
  let writeReqs := initZeroesUnpropagatedTransitions (state.threadTypes 0) addresses
state.applyTrace writeReqs

def mkPropagateTransitions : List RequestId → List ThreadId → List (Transition)
| writeReqIds, threads =>
  List.join $ writeReqIds.map λ wr => threads.foldl (λ reqs thId => (Pop.Transition.propagateToThread wr thId) :: reqs) []

def SystemState.initZeroesPropagateTransitions : SystemState → List Address → List (Transition)
  | state, addresses =>
  let reqs := filterNones $ state.requests.val.toList
  -- this filter should be uneccessary if SystemState is empty
  let writeReqs := reqs.filter (λ req => req.isWrite && addresses.elem req.address?.get! && req.value? == some 0)
  let writeReqIds := writeReqs.map Request.id
  let threads := state.threads.removeAll [0]
  mkPropagateTransitions writeReqIds threads

def SystemState.initZeroesPropagate! : SystemState → List Address → SystemState
  | state, addresses => state.applyTrace! $ state.initZeroesPropagateTransitions addresses
def SystemState.initZeroesPropagate : SystemState → List Address → Except String (SystemState)
  | state, addresses => state.applyTrace $ state.initZeroesPropagateTransitions addresses

def SystemState.initZeroes! : SystemState → List Address → SystemState
  | state, addresses =>
    let unpropagated := state.initZeroesUnpropagated! addresses
    unpropagated.initZeroesPropagate! addresses

def SystemState.initZeroes : SystemState → List Address → Except String (SystemState)
  | state, addresses =>
    let unpropagated := state.initZeroesUnpropagated addresses
    Except.bind  unpropagated (λ st => st.initZeroesPropagate addresses)

structure RequestSyntax where
  (reqKind : String)
  (reqType : String)
  (varName : String)
  (value : Option Nat)

instance : ToString RequestSyntax where toString := λ rs => s!"{rs.reqKind}, {rs.reqType}, {rs.varName}, {rs.value}"

-- TODO: I should refactor createLitmus to use something like this, but more robust (passing the maps)
def mkRequestSimple : RequestSyntax → ThreadId → String → List Transition
  | syn => match syn.varName with
    | "x" => Pop.mkRequest (syn.reqKind, syn.reqType, 0, syn.value)
    | "y" => Pop.mkRequest (syn.reqKind, syn.reqType, 1, syn.value)
    | "z" => Pop.mkRequest (syn.reqKind, syn.reqType, 2, syn.value)
    | "" => Pop.mkRequest (syn.reqKind, syn.reqType, 42, syn.value)
    | v => panic! s!"Unsupported variable in guide: {v}"

structure LitmusMetadata where
  (name : String := "anonymous")
  (allowed : Litmus.AxiomaticAllowed := .unknown)
  (guideTraceGens : List (List (ThreadId × (String → List Transition))) := [])

def createLitmus (list : List (List RequestSyntax))
  (opScopesThreadMapping : Option $ ValidScopes × (ThreadId → String))
  (metadata : LitmusMetadata) : Litmus.Test :=
  let validScopes := opScopesThreadMapping.map λ (s,_) => s
  let threadTypes := match opScopesThreadMapping with
    | none => λ _ => "default"
    | some (_,f) => f
  let variablesRaw := list.map λ thread => thread.map (λ r => if r.varName.length == 0 then none else some r.varName)
  let variables := removeDuplicates $ filterNones $ List.join variablesRaw
  let variableNums := variables.zip (List.range variables.length)
  let variableMap := Std.mkHashMap (capacity := variableNums.length) |> variableNums.foldl λ acc (k, v) => acc.insert k v
  let replaceVar := λ r => match variableMap.find? r.varName with
    | some varName => (r.reqKind, r.reqType, varName ,r.value)
    | none => (r.reqKind, r.reqType, 0 ,r.value)
  let replacedVariablesNat : List (List (String × String × Nat × Option Nat)) :=  list.map λ thread => thread.map replaceVar
  let replacedVariables : List (List (String × String × Address × Value)) := replacedVariablesNat.map λ l => l.map (λ (str,rtype,addr,val) => (str,rtype,Address.ofNat addr, val))
  let fullThreads := replacedVariables.zip (List.range replacedVariables.length)
  let mkThread := λ (reqs, thId) => List.join $ List.map (λ r => mkRequest r thId (threadTypes thId)) reqs
  let mkOutcomeThread := λ (reqs, thId) => filterNones $ List.map (λ r => mkReadOutcomeTriple r thId) reqs
  let reqs := fullThreads.map λ t => mkThread t |>.toArray
  let outcomes := mkOutcome $ List.join $ fullThreads.map λ t => mkOutcomeThread t
  let initWrites := initZeroesUnpropagatedTransitions (threadTypes 0) (List.range variables.length)
  let initPropagates :=  mkPropagateTransitions (List.range initWrites.length) (List.range fullThreads.length).tail! -- tail! : remove 0 because of accept
  let guideTraces : List (List Transition) := metadata.guideTraceGens.map λ tr =>
    List.join $ tr.map λ (thId, genFun) => genFun (threadTypes thId)
  let initState := match validScopes with
    | some scopes => SystemState.init scopes threadTypes
    | none => SystemState.init (mkValidScopes fullThreads.length) threadTypes
  { initTransitions := initWrites ++ initPropagates,
    program := reqs.toArray, expected := outcomes,
    initState, name := metadata.name, axiomaticAllowed := metadata.allowed, guideTraces}

macro_rules
  | `(`[req| $r ]) => `(request| $r)
  | `(`[req_seq| $r ]) => `(request_seq| $r)
  | `(`[req_set| $r ]) => `(request_set| $r)

-- syntax sepBy(request_seq,  "||") : request_set
-- TODO: should not require Compat!

macro_rules
 | `(request| R $x:ident $[// $v]?) =>
 `(RequestSyntax.mk "R" ""  $(Lean.quote x.getId.toString)  $(Lean.quote $ v.map λ s => s.getNat))
 | `(request| R. $t:ident $x:ident $[// $v]?) =>
 `(RequestSyntax.mk "R" $(Lean.quote t.getId.toString) $(Lean.quote x.getId.toString) $(Lean.quote $ v.map λ s => s.getNat))
 | `(request| W $x:ident = $y:num) =>
 `(RequestSyntax.mk "W" "" $(Lean.quote x.getId.toString) (some $y))
 | `(request| W. $t:ident $x:ident = $y:num) =>
 `(RequestSyntax.mk "W" $(Lean.quote t.getId.toString) $(Lean.quote x.getId.toString) (some $y))
 | `(request| Fence     ) =>
 `(RequestSyntax.mk "Fence" "" "" none)
 | `(request| Fence. $t    ) =>
 `(RequestSyntax.mk "Fence" $(Lean.quote t.getId.toString) "" none)

macro_rules
  | `(request_seq| $r:request ) => do `([ `[req| $r] ])
  | `(request_seq| $r:request ; $rs:request_seq) => `(`[req| $r] :: `[req_seq| $rs])
  | `(request_seq| $r:request ;dep $rs:request_seq) => do
    let dep_syntax <- `(RequestSyntax.mk "Dependency" "" "" none)
    `(`[req| $r] :: $dep_syntax :: `[req_seq| $rs])

macro_rules
  | `(request_set| $r:request_seq ) => `([`[req_seq| $r]])
  | `(request_set| $r:request_seq || $rs:request_set) => `(`[req_seq| $r] :: `[req_set| $rs])

-- Hack : can't bind var in quotation for lambda
def propagateToThreadList : Pop.RequestId → Pop.ThreadId → String → List Pop.Transition :=
    λ r t _ => [Pop.Transition.propagateToThread r t]

macro_rules
  | `(`[transition| Accept ($r) at Thread $n]) => `( ($n, mkRequestSimple `[req|$r] $n ) )
  | `(`[transition| Propagate Request $r to Thread $t]) => `(($t, Pop.propagateToThreadList $r $t))
  | `(`[transition| Satisfy Request $r with Request $w]) => `((42, fun _ => [ (Pop.Transition.satisfyRead $r $w)]))

macro_rules
--  | `(`[guide_trace| $[$n:num],* ]) => `([ $[$n],* ])
  | `(`[guide_trace| [ $[$ts:transition],* ] ]) => `( [ $[`[transition|$ts]],* ])

--elab "litmusHints!" name:ident : term <= ty => do
--  mkHintElab litmusHintExtension name.getId ty
macro_rules
  | `(`[metadata| $name | ✓ $[$ms:litmus_metadata]?]) => match ms with
    | some mss => `( { `[metadata| $name | $mss] with allowed := (Litmus.AxiomaticAllowed.yes)})
    | none => `( { { guideTraceGens := litmusHints! $name, name := $(quote name.getId.toString) : Pop.LitmusMetadata} with allowed := (Litmus.AxiomaticAllowed.yes)})
  | `(`[metadata| $name | 𐄂 $[$ms:litmus_metadata]?]) => match ms with
    | some mss => `( { `[metadata| $name | $mss] with allowed := (Litmus.AxiomaticAllowed.no)})
    | none => `( { { guideTraceGens := litmusHints! $name, name := $(quote name.getId.toString) : Pop.LitmusMetadata} with allowed := (Litmus.AxiomaticAllowed.no)})

-- TODO: is there a more elegant way to do this with `Option.map`?
macro_rules
  | `(`[litmus|  {| $r |} $[where sys := $opdesc:system_desc ]? $[$opmeta:litmus_metadata]? $name:ident ]) => do
    let desc ← match opdesc with
    | none => `( Option.none)
    | some desc => `( (some `[sys| $desc]))
    let meta ← match opmeta with
    | none => `( { name := $(quote name.getId.toString) : Pop.LitmusMetadata })
    | some m => `( `[metadata| $name| $m] )
    `( createLitmus `[req_set| $r] $desc $meta)


def threadsGetAllNames (threadsSyntax : TSyntax `threads) : Array String :=
  match threadsSyntax.raw with
  | `(threads| $[$ts],*) => ts.map λ i => i.getId.toString
  | _ => unreachable! -- #[]

partial def systemDescGetAllNames (descSyn : TSyntax `system_desc) : Array String :=
  match descSyn.raw with
    | `(system_desc| { $ts:threads }) => threadsGetAllNames ts
    | `(system_desc| { $ts:threads }.$_) => threadsGetAllNames ts
    | `(system_desc| { $[$sds:system_desc],* }) => sds.map systemDescGetAllNames |>.foldl
      Array.append #[]
    | _ => unreachable!
-- TODO: see if I can use Lean.mkNameMap?
def mkNameMapping (names : Array String) : String → Option ThreadId :=
  λ s => List.range names.size |>.foldl
    (init := none)
    λ old i => if names[i.toNat]! == s
      then some i
      else old

def mkCTA (mapping : String → Option ThreadId) (threads : TSyntax `threads)
  : Except String (ListTree ThreadId) :=
  let threadNats := threadsGetAllNames threads |>.toList |>.map mapping
  if threadNats.contains none
    then Except.error "Invalid thread string to id mapping"
    else Except.ok $ ListTree.leaf $ filterNones threadNats

def mkThreadTypeFun : List (List ThreadId × String) → ThreadId → String
  | [], _ => "unknown"
  | (ids,s)::rest, thId => if ids.contains thId then s else mkThreadTypeFun rest thId

partial def mkSysAux (mapping : String → Option ThreadId) (desc : TSyntax `system_desc)
  : Except String ((ListTree ThreadId) × (List $ (List String) × String)) :=
  match desc.raw with
    | `(system_desc| { $ts:threads }) => return (← mkCTA mapping ts, [(threadsGetAllNames ts |>.toList, "default")])
    | `(system_desc| { $ts:threads }.$ty) => return (← mkCTA mapping ts, [(threadsGetAllNames ts |>.toList, ty.getId.toString)])
    | `(system_desc| { $[$sds:system_desc],* }) => do
      let (sdsTrees, names) := (← sds.mapM $ mkSysAux mapping).toList.unzip
      let join := blesort $ setJoin $ sdsTrees.map (@ListTree.listType ThreadId instBEqThreadId)
      return (← @ListTree.mkParent ThreadId instBEqThreadId join sdsTrees, names.join)
    | _ => Except.error "unexpected syntax in system description"

def mkSys (desc : TSyntax `system_desc) : Except String (ValidScopes × (List $ List ThreadId × String)) :=
  let allNames := systemDescGetAllNames desc |>.qsort alphabetic
  let mapping := mkNameMapping allNames
  if allNames.toList.unique.length == allNames.size
  then do
    let (scopes, thTypes) ← mkSysAux mapping desc
    let threads := filterNones (allNames.map mapping).toList
    let thIdTypes := thTypes.map λ (thNames,ty) => (thNames.map mapping |> filterNones, ty)
    return ({ scopes := scopes, system_scope := threads}, thIdTypes)
  else
    let doubles := allNames.toList.unique.foldl (init := allNames) (λ curr name => curr.erase name)
    Except.error s!"some thread(s) appear(s) more than once: {doubles}"

macro_rules
  | `(`[sys| $desc:system_desc ]) => do
    let descRes := mkSys desc
    match descRes with
      | Except.ok (lt,thTy) => `(($(quote lt), mkThreadTypeFun $(quote thTy)))
      | Except.error msg => Macro.throwError msg

-- Tests
-- #eval `[sys| {{ T1, T2 } , {T3}.x86, {T4, T5, T6}} ].scopes
-- should fail!
-- #eval `[sys| {{ T1, T2 } , {T2, T3}} ].scopes.leaves

end Pop
