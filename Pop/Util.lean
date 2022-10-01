import Lean
open Std.HashMap

namespace Util

theorem n_minus_one_le_n {n : Nat} : n > 0 → n - 1 < n := by
  cases n with
  | zero => simp []
  | succ n =>
    intros
    rw [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    apply Nat.le.refl

def filterNones {α : Type} : List (Option α) → List α
  | none::rest => filterNones rest
  | (some val):: rest => val::(filterNones rest)
  | [] => []

def Array.sum : Array Nat → Nat
  | arr => arr.foldl (init := 0) (· + ·)

def filterNonesArr {α : Type} : Array (Option α) → Array α
  | arr => arr.toList |> filterNones |>.toArray

def blesort : List Nat → List Nat
  | as => Array.toList $ Array.qsort as.toArray (λ x y => Nat.ble x y)

-- TODO: probably horribly slow!
def alphabetic : String → String → Bool
  | ⟨a::as⟩, ⟨b::bs⟩ => a < b || (a == b) && alphabetic ⟨as⟩ ⟨bs⟩
  | ⟨[]⟩, _ => true
  | ⟨_::_⟩, _ => false

def lexBLt : Nat × Nat → Nat × Nat → Bool
  | (n₁,n₂), (m₁,m₂) => Nat.blt n₁ m₁ || ((n₁ == m₁) && Nat.blt n₂ m₂)

def lexBLe : Nat × Nat → Nat × Nat → Bool
| n, m => lexBLt n m || n == m

partial def removeDuplicates [BEq α] : List α → List α
  | [] => []
  | (x :: xs) => x :: removeDuplicates (xs.filter (λ y => y != x))

def _root_.List.sublist [BEq α] : List α → List α → Bool
  | l₁, l₂ => l₁.all (λ e => l₂.elem e)

def _root_.List.setEq [BEq α] : List α → List α → Bool
  | l₁, l₂ => l₁.sublist l₂ && l₂.sublist l₁

def _root_.List.countOcurrences [BEq α] : List α → List (α × Nat)
  | [] => []
  | x::xs =>
    let rest := xs.countOcurrences
    match rest.lookup x with
    | some num => (x, num + 1)::rest
    | none => (x,1)::rest

def setJoinPair [BEq α] (l₁ l₂ : List α) : List α :=
  match l₁, l₂ with
  | l₁, [] => l₁
  | [], l₂ => l₂
  | a::as, b::bs => match as.contains b, bs.contains a with
    | true, true => setJoinPair as bs
    | false, true => b :: setJoinPair as bs
    | true, false => a :: setJoinPair as bs
    | false, false => a :: b :: setJoinPair as bs

def setJoin [BEq α] (ls : List (List α)) : List α :=
  ls.foldl (init := []) setJoinPair

def colorRed : String → String :=
  λ str => "\x1b[37;41m" ++ str ++ "\u001b[0m"

def colorGreen : String → String :=
  λ str => "\x1b[37;42m" ++ str ++ "\u001b[0m"

-- Removed sublist condition from type as it made programming
-- with this basically impossible...
inductive ListTree (α : Type) [BEq α] : Type
  | leaf : List α → ListTree α
  | parentNil : List α → ListTree α
  | parentCons : ListTree α → ListTree α → ListTree α
  deriving Repr

open Lean in
private def quoteListTree [Quote α] [BEq α] : ListTree α → Term
  | .leaf a => Syntax.mkCApp ``ListTree.leaf #[quote a]
  | .parentNil a => Syntax.mkCApp ``ListTree.parentNil #[quote a]
  | .parentCons child sibs => Syntax.mkCApp ``ListTree.parentCons
    #[quoteListTree child, quoteListTree sibs]

instance {α : Type} [BEq α] [Lean.Quote α] : Lean.Quote (ListTree α) where quote := quoteListTree

def ListTree.beq {α : Type} [BEq α] : ListTree α → ListTree α → Bool
  | .leaf a, .leaf b => a.setEq b
  | .parentNil a, .parentNil b => a.setEq b
  | .parentCons child₁ sibs₁, .parentCons child₂ sibs₂ => (beq child₁ child₂) && (beq sibs₁ sibs₂)
  | _, _ => false

instance {α : Type} [BEq α]  : BEq (ListTree α) where beq := ListTree.beq

-- TODO: this does not check it is well-formed...
def ListTree.listType [BEq α] : ListTree α  → List α
  | leaf l => l
  | parentNil l => l
  | parentCons _ siblings => listType siblings

def ListTree.mkParent {α : Type} [BEq α]
  (parent : List α) (children : List (ListTree α)) : Except String (ListTree α) := do
  let parentType := setJoin $ children.map ListTree.listType
  unless parentType.sublist parent do
    throw s!"Error appending. It has a non-sublist child."
  let parent := ListTree.parentNil parent
  return children.foldl (init := parent) λ sib ch => ListTree.parentCons ch sib

def Array.pmap : (α → β) → Array α → Array β
  | f, as =>
    let ts := as.map λ a => Task.spawn (λ _ => f a);
    let rs := ts.map Task.get;
    rs

open ListTree

def ListTree.elem [BEq α] :  List α → ListTree α → Bool
| val, leaf val' => val == val'
| val, parentNil val' => val == val'
| val, parentCons child siblings => elem val child || elem val siblings

instance [BEq α] : Membership (List α) (ListTree α) where
  mem lst tree := tree.elem lst = true

def ListTree.leaves [BEq α] :  ListTree α → List (List α)
  | leaf val => [val]
  | parentNil _ => []
  | parentCons child siblings => leaves child ++ leaves siblings

def ListTree.toList [BEq α] :  ListTree α → List (List α)
  | leaf val => [val]
  | parentNil val => [val]
  | parentCons child siblings => toList child ++ toList siblings

def ListTree.nodesAbove [BEq α] (lt :  ListTree α) (lst : List α) : List (List α) :=
  match lt with
  | leaf val => if List.sublist lst val then [val] else []
  | parentNil val => if List.sublist lst val then [val] else []
  | parentCons child siblings => (nodesAbove child lst) ++ (nodesAbove siblings lst)

def ListTree.nodesBelow [BEq α] (lt :  ListTree α) (lst : List α) : List (List α) :=
  match lt with
  | leaf val => if List.sublist val lst then [val] else []
  | parentNil val => if List.sublist val lst then [val] else []
  | parentCons child siblings => (nodesBelow child lst) ++ (nodesBelow siblings lst)

def ListTree.meet [BEq α] : ListTree α → α → α → Option (List α)
  | leaf val, a, b => if (val.elem a && val.elem b) then (some val) else none
  | parentNil val, a, b => if (val.elem a && val.elem b) then (some val) else none
  | parentCons child siblings, a, b =>
    let childRes := meet child a b
    match childRes with
      | res@(some _) => res
      | none => meet siblings a b

private def ListTree.toStringAux [BEq α] [ToString α] : ListTree α → String
   | .leaf val => String.intercalate ", " (val.map ToString.toString)
   | .parentNil val => String.intercalate ", " (val.map ToString.toString)
   | .parentCons child parent@(parentNil _) => "[" ++
     (toStringAux parent) ++ "] = [" ++ (toStringAux child) ++ "]"
   | .parentCons child siblings => (toStringAux siblings) ++ ", ["
     ++ (toStringAux child) ++ "]"

def ListTree.toString [BEq α] [ToString α] (lt : ListTree α) : String :=
  "[" ++ toStringAux lt ++ "]"

instance [BEq α] [ToString α] : ToString (ListTree α) where toString := ListTree.toString

/-
theorem List.sublist_trans [BEq α] (a b c : List α) : sublist a b → sublist b c → sublist a c := by
  intros hab hbc
  induction a <;> induction b <;> induction c <;> simp [List.sublist, List.all, List.foldr, List.elem] <;> try contradiction
  sorry  -- TODO
-/

structure Triple (α β γ : Type) where
 fst : α
 snd : β
 trd : γ

notation "(" a "," b "," c ")t" => Triple.mk a b c

def TupleTuple2Triple {α β γ : Type} : (α × β) × γ → Triple α β γ
 | ((a, b), c) => (a,b,c)t

def TupleTuple'2Triple {α β γ : Type} : α × (β × γ) → Triple α β γ
 | (a, (b, c)) => (a,b,c)t

instance {α β γ : Type} : Coe ((α × β) × γ)  (Triple α β γ) where coe := TupleTuple2Triple
instance {α β γ : Type} : Coe (α × (β × γ))  (Triple α β γ) where coe := TupleTuple'2Triple

-- def ListTree.joinSub [BEq α] {l₁ l₂: List α} (h : List.sublist l₁ l₂) : ListTree α l₁ → ListTree α l₂ → ListTree α l₂
--   | (leaf l₁), (parentNil l₂) => parentCons (leaf l₁) (parentNil l₂) h
--   | (leaf l₁), (leaf l₂) => parentCons (leaf l₁) (parentNil l₂) h
--   | (leaf l₁), parentCons (children : ListTree α child) (siblings : ListTree α l₂) sub =>
--     let hchild := List.sublist_trans sub 
-- 
--   parentCons (joinSub sub (leaf l₁) children) siblings sub
  

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

def exceptIO  {α : Type} [Inhabited α] : Except String α → IO α
  | exAlpha => match exAlpha with
    | Except.ok a => return a
    | Except.error msg => do
      IO.println msg
      return default


def selectLoop {α : Type 0} : String → (String → Except String α) → IO.FS.Stream → IO (Option α)
  | selectionString, selectFun, inputStream => do
  let mut selected := Except.error "unread"
  while !selected.isOk do
    IO.println selectionString
    let input <- inputStream.getLine
    if input.length == 0 then
      return none
    selected := selectFun input
    if let Except.error msg := selected then
      IO.println s!"Error: {msg}"
  match selected with
    | .ok a => return (some a)
    | _ => return none

def _root_.List.unique {α : Type 0} [BEq α] : List α → List α
  | [] => []
  | a :: as => if as.contains a then as.unique else (a :: as.unique)

def _root_.List.containsSet {α : Type 0} [BEq α] : List (List α) → List α → Bool
  | head::tail, l => head.setEq l || tail.containsSet l
  | [], _ => false

def _root_.List.uniqueSet {α : Type 0} [BEq α] : List (List α) → List (List α)
  | [] => []
  | a :: as => if as.containsSet a then as.uniqueSet else (a :: as.uniqueSet)

def _root_.List.revlookup [BEq β] : β → List (α × β) → Option α
  | _, []        => none
  | a, (k,b)::es => match a == b with
    | true  => some k
    | false => revlookup a es

structure ScopedBinaryRelation (α β : Type 0) [Hashable α] [BEq α] [Hashable β] [BEq β] where
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
def ltest2 := ListTree.parentCons ltest (ListTree.parentNil [1,2,3,4])
def ltest3 := ListTree.parentCons (ListTree.leaf [1,4]) ltest2

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
