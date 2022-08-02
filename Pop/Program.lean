import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Std.Data
import Pop.Exploration
open Std.HashMap
open Util

namespace Pop

inductive DefaultReqType
  | mk : DefaultReqType
  deriving BEq, Inhabited

instance : ArchReq where
  type := DefaultReqType
  beq_inst := instBEqDefaultReqType
  inhabited_inst := instInhabitedDefaultReqType

def mkRead (addr : Address) : BasicRequest :=
  let rr : ReadRequest := { addr := addr, reads_from := none, val := none}
  BasicRequest.read rr default

def mkWrite (addr : Address) (val : Value) : BasicRequest :=
  let wr : WriteRequest := { addr := addr, val := val}
  BasicRequest.write wr default

def mkBarrier : BasicRequest := BasicRequest.barrier default

-- TODO: Add values to writes
def mkRequest : String × Address × Value → ThreadId → Option (Transition)
  | ("R", addr, _), thId  => some $ Pop.Transition.acceptRequest (Pop.mkRead addr) thId
  | ("W", addr, val), thId  => some $ Pop.Transition.acceptRequest (Pop.mkWrite addr val) thId
  | ("Fence", _, _), thId => some $ Pop.Transition.acceptRequest (Pop.mkBarrier) thId
  | _, _ => none

def initZeroesUnpropagatedTransitions : List Address → List (Transition)
  | addresses =>
  -- Does the threadId matter? For now, using 0
  addresses.map λ addr => Pop.Transition.acceptRequest (Pop.mkWrite addr 0) 0

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
  let threads := state.system.threads.removeAll [0]
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

-- create accepts in a per-thread basis
def createAcceptList : List (List (String × String × Nat)) → List (Transition) × Array (Array (Transition))
  | list =>
  let variablesRaw := list.map λ thread => thread.map (λ r => if r.2.1.length == 0 then none else some r.2.1)
  let variables := removeDuplicates $ filterNones $ List.join variablesRaw
  let variableNums := variables.zip (List.range variables.length)
  let variableMap := Std.mkHashMap (capacity := variableNums.length) |> variableNums.foldl λ acc (k, v) => acc.insert k v
  let replaceVar := λ (req,var,val) => (req, (Option.get! $ variableMap.find? var),val)
  let replacedVariablesNat : List (List (String × Nat × Nat)) := list.map λ thread => thread.map replaceVar
  let replacedVariables : List (List (String × Address × Value)) := replacedVariablesNat.map λ l => l.map (λ (str,addr,val) => (str,Address.ofNat addr, Value.ofNat val))
  let fullThreads := replacedVariables.zip (List.range replacedVariables.length)
  let mkThread := λ (reqs, thId) => filterNones $ List.map (λ r => mkRequest r thId) reqs
  let reqs := fullThreads.map λ t => mkThread t |>.toArray
  let initWrites := initZeroesUnpropagatedTransitions (List.range variables.length)
  let initPropagates :=  mkPropagateTransitions (List.range initWrites.length) (List.range fullThreads.length).tail! -- tail! : remove 0 because of accept
  (initWrites ++ initPropagates, reqs.toArray)

declare_syntax_cat request
declare_syntax_cat request_seq
declare_syntax_cat request_set
syntax "R" ident : request
syntax "W" ident "=" num : request
syntax "Fence"   : request
syntax request ";" request_seq : request_seq
syntax request : request_seq
syntax request_seq "||" request_set : request_set
syntax request_seq : request_set
syntax "<|" request_set "|>" : term

-- syntax sepBy(request_seq,  "||") : request_set
open Lean.TSyntax.Compat

macro_rules
 | `(request| R $x:ident) => `(("R", $(Lean.quote x.getId.toString), 0))
 | `(request| W $x:ident = $y:num) => `(("W", $(Lean.quote x.getId.toString), $y))
 | `(request| Fence     ) => `(("Fence", "", 0))

macro_rules
  | `(request_seq| $r:request ) => do `([$(← Lean.expandMacros r)])
  | `(request_seq| $r:request ; $rs:request_seq) => `($r :: $rs)

macro_rules
  | `(request_set| $r:request_seq ) => `([$r])
  | `(request_set| $r:request_seq || $rs:request_set) => `($r :: $rs)
macro_rules
  | `(<| $r |>) => `( createAcceptList $r)
