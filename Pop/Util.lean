import Std
open Std.HashMap

namespace Util

def filterNones {α : Type} : List (Option α) → List α
  | none::rest => filterNones rest
  | (some val):: rest => val::(filterNones rest)
  | [] => []

partial def removeDuplicates [BEq α] : List α → List α
  | [] => []
  | (x :: xs) => x :: removeDuplicates (xs.filter (λ y => y != x))

def List.sublist [BEq α] : List α → List α → Bool
  | l₁, l₂ => l₁.all (λ e => l₂.elem e)

inductive ListTree (α : Type) [BEq α] : List α → Type
  | leaf (val : List α) : ListTree α val
  | parentNil  (val : List α) : ListTree α val
  | parentCons (_ : ListTree α child) (_ : ListTree α sibling)
  (_ : List.sublist child sibling) : ListTree α sibling

open ListTree

def ListTree.elem [BEq α] {l : List α} :  List α → ListTree α l → Bool
| val, leaf val' => val == val'
| val, parentNil val' => val == val'
| val, parentCons child sibling _ => elem val child || elem val sibling

instance [BEq α] {l : List α} : Membership (List α) (ListTree α l) where
  mem lst tree := tree.elem lst = true

def ListTree.leaves [BEq α] {l : List α} :  ListTree α l → List (List α)
| leaf val => [val]
| parentNil _ => []
| parentCons child sibling _ => leaves child ++ leaves sibling


def ListTree.meet [BEq α] {l : List α} : ListTree α l → α → α → Option (List α)
  | leaf val, a, b => if (val.elem a && val.elem b) then (some val) else none
  | parentNil val, a, b => if (val.elem a && val.elem b) then (some val) else none
  | parentCons child sibling _, a, b =>
    let childRes := meet child a b
    match childRes with
      | res@(some _) => res
      | none => meet sibling a b

def ListTree.joinSub [BEq α] {l₁ l₂: List α} (h : List.sublist l₁ l₂) : ListTree α l₁ → ListTree α l₂ → ListTree α l₂
  | t1@(leaf l₁), t₂@(parentNil l₂) => parentCons (leaf l₁) ()
  

-- def ListTree.mkAux [BEq α] {l₁ l₂ : List α} : List (List α) → ListTree α l₁ → ListTree α l₂
--   --| lists, subtree => subtree
--   sorry
-- 
-- def ListTree.mk [BEq α] {l : List α} : List (List α) → ListTree α l
--   | lists =>
--     let sorted := lists.toArray.qsort List.sublist
--     match sorted.reverse.toList with
--       | [] => leaf []
--       | head :: rest => parentNil head

structure ScopedBinaryRelation (α β : Type) [Hashable α] [BEq α] [Hashable β] [BEq β] where
  val : Std.HashMap (α × β × β) Bool
  defaultRes : Bool

variable {α β : Type} [Hashable α] [BEq α] [Hashable β] [BEq β]
def ScopedBinaryRelation.default : ScopedBinaryRelation α β := ScopedBinaryRelation.mk (Std.mkHashMap) false

instance : Inhabited (ScopedBinaryRelation α β) where default := ScopedBinaryRelation.default

def ScopedBinaryRelation.update : ScopedBinaryRelation α β → α → β → β → ScopedBinaryRelation α β
  | rel, s, x,y =>
    let val' := rel.val.insert (s,(x,y)) true
    { rel with val := val'}

def ScopedBinaryRelation.lookup : ScopedBinaryRelation α β → α → β → β → Bool
  | rel, s, x, y => match rel.val[(s,(x,y))] with
    | some res => res
    | none => rel.defaultRes

notation rel "[" s "," x "," y "]:=" val => ScopedBinaryRelation.update rel s x y val

def ltest := ListTree.leaf [1,2,4]
def proofltest2 : List.sublist [1,2,4] [1,2,3,4] = true := by simp
def proofltest3 : List.sublist [1,4] [1,2,3,4] = true := by simp
def ltest2 := ListTree.parentCons ltest (ListTree.parentNil [1,2,3,4]) proofltest2
def ltest3 := ListTree.parentCons (ListTree.leaf [1,4]) ltest2 proofltest3

#eval ListTree.elem [1,2,4] ltest
#eval ListTree.elem [1,2,4] ltest2
#eval ListTree.elem [1,2,3,4] ltest2
#eval ListTree.elem [1,3,4] ltest2
#eval ListTree.elem [1,3,4] ltest3
#eval ListTree.elem [1,2,4] ltest2
#eval ltest2.leaves
#eval ltest3.leaves
#eval ltest3.meet 1 2
#eval ltest3.meet 1 4
#eval ltest3.meet 1 3
#eval ltest3.meet 1 5

end Util
