
namespace Util

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
