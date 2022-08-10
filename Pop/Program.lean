import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Std.Data
--import Pop.TSO -- TODO: make this arch parametric too

open Std.HashMap
open Util

namespace Pop

variable [Arch]

class LitmusSyntax where
  mkRead : String → Address → BasicRequest
  mkWrite : String → Address → Value → BasicRequest
  mkBarrier : String → BasicRequest

variable [LitmusSyntax]
open LitmusSyntax

def mkRequest : String × String × Address × Value → ThreadId → Option (Transition)
  | ("R", typeStr, addr, _), thId  => some $ Pop.Transition.acceptRequest (mkRead typeStr addr) thId
  | ("W",typeStr , addr, val), thId  => some $ Pop.Transition.acceptRequest (mkWrite typeStr addr val) thId
  | ("Fence", typeStr, _, _), thId => some $ Pop.Transition.acceptRequest (mkBarrier typeStr) thId
  | _, _ => none

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
  (value : Nat)

-- create accepts in a per-thread basis
def createAcceptList : List (List RequestSyntax) → List (Transition) × ProgramState
  | list =>
  let variablesRaw := list.map λ thread => thread.map (λ r => if r.varName.length == 0 then none else some r.varName)
  let variables := removeDuplicates $ filterNones $ List.join variablesRaw
  let variableNums := variables.zip (List.range variables.length)
  let variableMap := Std.mkHashMap (capacity := variableNums.length) |> variableNums.foldl λ acc (k, v) => acc.insert k v
  let replaceVar := λ r => (r.reqKind, r.reqType, (Option.get! $ variableMap.find? r.varName),r.value)
  let replacedVariablesNat : List (List (String × String × Nat × Nat)) := list.map λ thread => thread.map replaceVar
  let replacedVariables : List (List (String × String × Address × Value)) := replacedVariablesNat.map λ l => l.map (λ (str,rtype,addr,val) => (str,rtype,Address.ofNat addr, Value.ofNat val))
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
syntax "R." ident ident : request
syntax "W" ident "=" num : request
syntax "W." ident ident "=" num : request
syntax "Fence"   : request
syntax "Fence." ident  : request
syntax request ";" request_seq : request_seq
syntax request : request_seq
syntax request_seq "||" request_set : request_set
syntax request_seq : request_set
syntax "{|" request_set "|}" : term

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
 | `(request| R $x:ident) =>
 `(RequestSyntax.mk "R" ""  $(Lean.quote x.getId.toString)  0)
 | `(request| R. $t:ident $x:ident) =>
 `(RequestSyntax.mk "R" $(Lean.quote t.getId.toString) $(Lean.quote x.getId.toString) 0)
 | `(request| W $x:ident = $y:num) =>
 `(RequestSyntax.mk "W" "" $(Lean.quote x.getId.toString) $y)
 | `(request| W. $t:ident $x:ident = $y:num) =>
 `(RequestSyntax.mk "W" $(Lean.quote t.getId.toString) $(Lean.quote x.getId.toString) $y)
 | `(request| Fence     ) =>
 `(RequestSyntax.mk "Fence" "" "" 0)
 | `(request| Fence. $t    ) =>
 `(RequestSyntax.mk "Fence" $(Lean.quote t.getId.toString) "" 0)

macro_rules
  | `(request_seq| $r:request ) => do `([ `[req| $r] ])
  | `(request_seq| $r:request ; $rs:request_seq) => `(`[req| $r] :: `[req_seq| $rs])

macro_rules
  | `(request_set| $r:request_seq ) => `([`[req_seq| $r]])
  | `(request_set| $r:request_seq || $rs:request_set) => `(`[req_seq| $r] :: `[req_set| $rs])

macro_rules
  | `({| $r |}) => `( createAcceptList `[req_set| $r])
