import Pop.Util
import Pop.Pop
import Pop.States
import Lean
import Pop.Util

open Std.HashMap
open Util

namespace Litmus
open Util Pop

variable [Arch]
abbrev Outcome := List $ ThreadId × Address × Value
inductive AxiomaticAllowed
  | yes
  | no
  | unknown

structure Test where
 (initTransitions : List Transition)
 (program : ProgramState)
 (expected : Outcome)
 (initState : SystemState)
 (name : String)
 (axiomaticAllowed : AxiomaticAllowed)

def addressValuePretty : Address × Value → String
  | (_, none) => "invalid outcome!"
  | (addr, some val) => s!"{addr.prettyPrint} = {val}"

def Outcome.prettyPrint : Litmus.Outcome → String
  | outcome =>
  let threads : List Litmus.Outcome := outcome.groupBy (·.1 == ·.1)
  let threadStrings := threads.map
    λ th => String.intercalate "; " $ th.map (addressValuePretty $ Prod.snd ·)
  String.intercalate " || " threadStrings

-- Assumes each value written at most once per address!
def Outcome.toRFPairs (outcome : Litmus.Outcome) (prog : ProgramState)
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

end Litmus

notation "✓"  => Litmus.AxiomaticAllowed.yes
notation "×"  => Litmus.AxiomaticAllowed.no


namespace Pop

variable [Arch]

class LitmusSyntax where
  mkRead : String → Address → BasicRequest
  mkWrite : String → Address → Value → BasicRequest
  mkBarrier : String → BasicRequest

def mkValidScopes (n : Nat) : ValidScopes :=
  { system_scope := List.range n, scopes := ListTree.leaf (List.range n)}

variable [LitmusSyntax]
open LitmusSyntax

def mkRequest : String × String × Address × Value → ThreadId → Option (Transition)
  | ("R", typeStr, addr, _), thId  => some $ Pop.Transition.acceptRequest (mkRead typeStr addr) thId
  | ("W",typeStr , addr, val), thId  => some $ Pop.Transition.acceptRequest (mkWrite typeStr addr val) thId
  | ("Fence", typeStr, _, _), thId => some $ Pop.Transition.acceptRequest (mkBarrier typeStr) thId
  | ("Dependency", _, _, _), _ => some $ Pop.Transition.dependency none
  | _, _ => none

def mkOutcome : String × String × Address × Value → ThreadId → Litmus.Outcome
  | ("R", _, addr, val@(some _)), thId  => [(thId,addr,val)]
  | _, _ => []

def initZeroesUnpropagatedTransitions : List Address → List (Transition)
  | addresses =>
  -- Does the threadId matter? For now, using 0
  addresses.map λ addr => Pop.Transition.acceptRequest (mkWrite "" addr 0) 0

def SystemState.initZeroesUnpropagated! : SystemState → List Address → SystemState
  | state, addresses =>
    let writeReqs := initZeroesUnpropagatedTransitions addresses
    state.applyTrace! writeReqs

def SystemState.initZeroesUnpropagated : SystemState → List Address → Except String (SystemState)
  | state, addresses =>
  let writeReqs := initZeroesUnpropagatedTransitions addresses
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

def createLitmus (list : List (List RequestSyntax))
  (validScopes : Option ValidScopes) (name : String)
  (axiomaticAllowed := Litmus.AxiomaticAllowed.unknown) : Litmus.Test :=
  let variablesRaw := list.map λ thread => thread.map (λ r => if r.varName.length == 0 then none else some r.varName)
  let variables := removeDuplicates $ filterNones $ List.join variablesRaw
  let variableNums := variables.zip (List.range variables.length)
  let variableMap := Std.mkHashMap (capacity := variableNums.length) |> variableNums.foldl λ acc (k, v) => acc.insert k v
  let replaceVar := λ r => (r.reqKind, r.reqType, (Option.get! $ variableMap.find? r.varName),r.value)
  let replacedVariablesNat : List (List (String × String × Nat × Option Nat)) := list.map λ thread => thread.map replaceVar
  let replacedVariables : List (List (String × String × Address × Value)) := replacedVariablesNat.map λ l => l.map (λ (str,rtype,addr,val) => (str,rtype,Address.ofNat addr, val))
  let fullThreads := replacedVariables.zip (List.range replacedVariables.length)
  let mkThread := λ (reqs, thId) => filterNones $ List.map (λ r => mkRequest r thId) reqs
  let mkOutcomeThread := λ (reqs, thId) => List.join $ List.map (λ r => mkOutcome r thId) reqs
  let reqs := fullThreads.map λ t => mkThread t |>.toArray
  let outcomes := List.join $ fullThreads.map λ t => mkOutcomeThread t
  let initWrites := initZeroesUnpropagatedTransitions (List.range variables.length)
  let initPropagates :=  mkPropagateTransitions (List.range initWrites.length) (List.range fullThreads.length).tail! -- tail! : remove 0 because of accept
  let initState := match validScopes with
    | some scopes => SystemState.init scopes
    | none => SystemState.init $ mkValidScopes fullThreads.length
  { initTransitions := initWrites ++ initPropagates,
    program := reqs.toArray, expected := outcomes,
    initState, name, axiomaticAllowed}

declare_syntax_cat request
declare_syntax_cat request_seq
declare_syntax_cat request_set
declare_syntax_cat threads
declare_syntax_cat system_desc

syntax "R" ident ("//" num)? : request
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

syntax "{|" request_set "|}" ("where" "sys" ":=" system_desc )? : term
syntax "`[sys|" system_desc "]" : term
syntax "`[req|" request "]" : term
syntax "`[req_seq|" request_seq "]" : term
syntax "`[req_set|" request_set "]" : term
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

-- TODO: is there a more elegant way to do this with `Option.map`?
macro_rules
  | `({| $r |} $[where sys := $opdesc:system_desc ]?) => match opdesc with
    | none => `( createLitmus `[req_set| $r] none )
    | some desc => `( createLitmus `[req_set| $r] (some `[sys| $desc]))

macro "deflitmus" name:ident " := " litmus:term : command => `(def $name := $litmus $(Lean.quote name.getId.toString))

open Lean

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

partial def mkSysAux (mapping : String → Option ThreadId) (desc : TSyntax `system_desc)
  : Except String (ListTree ThreadId) :=
  match desc.raw with
    | `(system_desc| { $ts:threads }) => mkCTA mapping ts
    | `(system_desc| { $ts:threads }.$_) => mkCTA mapping ts
    | `(system_desc| { $[$sds:system_desc],* }) => do
      let sdsTrees := (← sds.mapM $ mkSysAux mapping).toList
      let join := setJoin $ sdsTrees.map ListTree.listType
      ListTree.mkParent join sdsTrees
    | _ => Except.error "unexpected syntax in system description"

-- Define an attribute to add up all Litmus tests
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Stateful.2FAggregating.20Macros.3F/near/301067121
/-
builtin_initialize unusedVariablesIgnoreFnsExt : SimplePersistentEnvExtension Name Unit ←
  registerSimplePersistentEnvExtension {
    name          := `unusedVariablesIgnoreFns
    addEntryFn    := fun _ _ => ()
    addImportedFn := fun _ => ()
  }

builtin_initialize
  registerBuiltinAttribute {
    name  := `litmustest
    descr := "litmus test"
    add   := fun declName stx attrKind => do
      let env ← getEnv
      setEnv <| unusedVariablesIgnoreFnsExt.addEntry env decl
      let prio ← getAttrParamOptPrio stx[1]
      discard <| addSimpCongrTheorem declName attrKind prio |>.run {} {}
  }
-/

def mkSys (desc : TSyntax `system_desc) : Except String ValidScopes :=
  let allNames := systemDescGetAllNames desc |>.qsort alphabetic
  let mapping := mkNameMapping allNames
  if allNames.toList.unique.length == allNames.size
  then do
    let threads := filterNones (allNames.map mapping).toList
    let scopes ← mkSysAux mapping desc
    return { scopes := scopes, system_scope := threads}
  else
    let doubles := allNames.toList.unique.foldl (init := allNames) (λ curr name => curr.erase name)
    Except.error s!"some thread(s) appear(s) more than once: {doubles}"


macro_rules
  | `(`[sys| $desc:system_desc ]) => do
    let descRes := mkSys desc
    match descRes with
      | Except.ok lt => `($(quote lt))
      | Except.error msg => Macro.throwError msg

-- Tests
-- #eval `[sys| {{ T1, T2 } , {T3}.x86, {{T4, T5, T6}}} ].scopes.leaves
-- should fail!
-- #eval `[sys| {{ T1, T2 } , {T2, T3}} ].scopes.leaves

end Pop
