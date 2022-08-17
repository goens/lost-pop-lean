import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Pop.Litmus
import Std.Data

open Std.HashMap
open Util

namespace Pop

variable [Arch]

class LitmusSyntax where
  mkRead : String → Address → BasicRequest
  mkWrite : String → Address → Value → BasicRequest
  mkBarrier : String → BasicRequest
  mkInitState : Nat → SystemState

variable [LitmusSyntax]
open LitmusSyntax

def mkRequest : String × String × Address × Value → ThreadId → Option (Transition)
  | ("R", typeStr, addr, _), thId  => some $ Pop.Transition.acceptRequest (mkRead typeStr addr) thId
  | ("W",typeStr , addr, val), thId  => some $ Pop.Transition.acceptRequest (mkWrite typeStr addr val) thId
  | ("Fence", typeStr, _, _), thId => some $ Pop.Transition.acceptRequest (mkBarrier typeStr) thId
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

-- create accepts in a per-thread basis
def createLitmus : List (List RequestSyntax) → Litmus.Test
  | list =>
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
  let initState := mkInitState fullThreads.length
  ((initWrites ++ initPropagates, reqs.toArray), (outcomes, initState))

declare_syntax_cat request
declare_syntax_cat request_seq
declare_syntax_cat request_set
syntax "R" ident ("//" num)? : request
syntax "R." ident ident  ("//" num)? : request
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

macro_rules
  | `(request_set| $r:request_seq ) => `([`[req_seq| $r]])
  | `(request_set| $r:request_seq || $rs:request_set) => `(`[req_seq| $r] :: `[req_set| $rs])

macro_rules
  | `({| $r |}) => `( createLitmus `[req_set| $r])
