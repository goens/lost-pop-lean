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

def AxiomaticAllowed.toString : AxiomaticAllowed → String
  | yes => "✓"
  | no => "╳"
  | unknown => "?"

instance : ToString AxiomaticAllowed where toString := AxiomaticAllowed.toString

structure Test where
 (initTransitions : List Transition)
 (program : ProgramState)
 (expected : Outcome)
 (initState : SystemState)
 (name : String)
 (axiomaticAllowed : AxiomaticAllowed)

def Test.numThreads (test : Test) : Nat := test.program.size
def Test.numInstructions (test : Test) : Nat := Array.sum $ test.program.map (λ th => th.size)
def Test.numScopes (test : Test)  : Nat := test.initState.scopes.scopes.toList.length
def Test.weightedSize (test : Test)  : Nat := test.numThreads * 100 + test.numInstructions * 10 + test.numScopes

instance : Inhabited Test where default := { initTransitions := [], program := #[], expected := [], initState := default, name := "default", axiomaticAllowed := .unknown }

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

namespace Pop

variable [Arch]

class LitmusSyntax where
  mkRead : String → Address → String → BasicRequest
  mkWrite : String → Address → Value → String → BasicRequest
  mkBarrier : String → String → BasicRequest

def mkValidScopes (n : Nat) : ValidScopes :=
  { system_scope := List.range n, scopes := ListTree.leaf (List.range n)}

variable [LitmusSyntax]
open LitmusSyntax

def mkRequest : String × String × Address × Value → ThreadId → String → Option (Transition)
  | ("R", typeStr, addr, _), thId, thTy => some $ Pop.Transition.acceptRequest (mkRead typeStr addr thTy) thId
  | ("W",typeStr , addr, val), thId, thTy  => some $ Pop.Transition.acceptRequest (mkWrite typeStr addr val thTy) thId
  | ("Fence", typeStr, _, _), thId, thTy => some $ Pop.Transition.acceptRequest (mkBarrier typeStr thTy) thId
  | ("Dependency", _, _, _), _, _ => some $ Pop.Transition.dependency none
  | _, _, _ => none

def mkOutcome : String × String × Address × Value → ThreadId → Litmus.Outcome
  | ("R", _, addr, val@(some _)), thId  => [(thId,addr,val)]
  | _, _ => []

def initZeroesUnpropagatedTransitions : List Address → List (Transition)
  | addresses =>
  -- Does the threadId matter? For now, using 0
  addresses.map λ addr => Pop.Transition.acceptRequest (mkWrite "" addr 0 "init") 0

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
  (opScopesThreadMapping : Option $ ValidScopes × (ThreadId → String)) (name : String)
  (axiomaticAllowed := Litmus.AxiomaticAllowed.unknown) : Litmus.Test :=
  let validScopes := opScopesThreadMapping.map λ (s,_) => s
  let threadTypes := match opScopesThreadMapping with
    | none => λ _ => "default"
    | some (_,f) => f
  let variablesRaw := list.map λ thread => thread.map (λ r => if r.varName.length == 0 then none else some r.varName)
  let variables := removeDuplicates $ filterNones $ List.join variablesRaw
  let variableNums := variables.zip (List.range variables.length)
  let variableMap := Std.mkHashMap (capacity := variableNums.length) |> variableNums.foldl λ acc (k, v) => acc.insert k v
  let replaceVar := λ r => (r.reqKind, r.reqType, (Option.get! $ variableMap.find? r.varName),r.value)
  let replacedVariablesNat : List (List (String × String × Nat × Option Nat)) := list.map λ thread => thread.map replaceVar
  let replacedVariables : List (List (String × String × Address × Value)) := replacedVariablesNat.map λ l => l.map (λ (str,rtype,addr,val) => (str,rtype,Address.ofNat addr, val))
  let fullThreads := replacedVariables.zip (List.range replacedVariables.length)
  let mkThread := λ (reqs, thId) => filterNones $ List.map (λ r => mkRequest r thId (threadTypes thId)) reqs
  let mkOutcomeThread := λ (reqs, thId) => List.join $ List.map (λ r => mkOutcome r thId) reqs
  let reqs := fullThreads.map λ t => mkThread t |>.toArray
  let outcomes := List.join $ fullThreads.map λ t => mkOutcomeThread t
  let initWrites := initZeroesUnpropagatedTransitions (List.range variables.length)
  let initPropagates :=  mkPropagateTransitions (List.range initWrites.length) (List.range fullThreads.length).tail! -- tail! : remove 0 because of accept
  let initState := match validScopes with
    | some scopes => SystemState.init scopes threadTypes
    | none => SystemState.init (mkValidScopes fullThreads.length) threadTypes
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

syntax "{|" request_set "|}" ("where" "sys" ":=" system_desc )? ("✓")? : term
syntax "{|" request_set "|}" ("where" "sys" ":=" system_desc )? "╳" : term
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
  | `({| $r |} $[where sys := $opdesc:system_desc ]? ✓) => match opdesc with
    | none => `( createLitmus `[req_set| $r] none (axiomaticAllowed := .yes) )
    | some desc => `( createLitmus `[req_set| $r] (some `[sys| $desc]) (axiomaticAllowed := .yes))
  | `({| $r |} $[where sys := $opdesc:system_desc ]? ╳) => match opdesc with
    | none => `( createLitmus `[req_set| $r] none (axiomaticAllowed := .no))
    | some desc => `( createLitmus `[req_set| $r] (some `[sys| $desc]) (axiomaticAllowed := .no))

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
      let join := setJoin $ sdsTrees.map ListTree.listType
      return (← ListTree.mkParent join sdsTrees, names.join)
    | _ => Except.error "unexpected syntax in system description"

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

macro "deflitmus" name:ident " := " litmus:term : command => `(@[litmusTest $name] def $name := $litmus $(Lean.quote name.getId.toString))

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
