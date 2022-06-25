import Pop.States
import Lean
import Pop.Pop
import Pop.Util
import Std.Data
open Std.HashMap
open Util Pop

def mkRequest : String × Address → ThreadId → Option Transition
  | ("R", addr), thId  => some $ Pop.Transition.acceptRequest (Pop.mkRead addr) thId
  | ("W", addr), thId  => some $ Pop.Transition.acceptRequest (Pop.mkRead addr) thId
  | ("Fence", _), thId => some $ Pop.Transition.acceptRequest (Pop.mkBarrier) thId
  | _, _ => none

def createAcceptList : List (List (String × String)) → List Transition
  | list =>
  let variablesRaw := list.map λ thread => thread.map (λ r => if r.2.length == 0 then none else some r.2)
  let variables := removeDuplicates $ filterNones $ List.join variablesRaw
  let variableNums := variables.zip (List.range variables.length)
  let variableMap := Std.mkHashMap (capacity := variableNums.length) |> variableNums.foldl λ acc (k, v) => acc.insert k v
  let replaceVar := λ (req,var) => (req, 1 + (Option.get! $ variableMap.find? var))
  let replacedVariables : List (List (String × Nat)) := list.map λ thread => thread.map replaceVar
  let fullThreads := replacedVariables.zip (List.range replacedVariables.length)
  let mkThread := λ (reqs, thId) => filterNones $ reqs.map (λ r => mkRequest r thId)
  List.join $ fullThreads.map mkThread

declare_syntax_cat request
declare_syntax_cat request_seq
declare_syntax_cat request_set
syntax "R" ident : request
syntax "W" ident : request
syntax "Fence"   : request
syntax request ";" request_seq : request_seq
syntax request : request_seq
syntax request_seq "||" request_set : request_set
syntax request_seq : request_set
syntax "<|" request_set "|>" : term

-- syntax sepBy(request_seq,  "||") : request_set

macro_rules
 | `(request| R $x:ident) => `(("R", $(Lean.quote x.getId.toString)))
 | `(request| W $x:ident) => `(("W", $(Lean.quote x.getId.toString)))
 | `(request| Fence     ) => `(("Fence", ""))

macro_rules
  | `(request_seq| $r:request ) => `([$r])
  | `(request_seq| $r:request ; $rs:request_seq) => `($r :: $rs)

macro_rules
  | `(request_set| $r:request_seq ) => `([$r])
  | `(request_set| $r:request_seq || $rs:request_set) => `($r :: $rs)
macro_rules
  | `(<| $r |>) => `( createAcceptList $r)
