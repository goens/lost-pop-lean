import Pop.Program
import Pop.Util

open Util Pop

namespace Litmus



def IRIW := <| W x=1 ||  R x; R y || R y; R x || W y=1 |>
def MP := <| W x=0; W y=0; W x=1; W y=1 ||  R y; R x |>
def MP_fence1 := <| W x=0; W y=0; W x=1; Fence; W y=1 ||  R y; R x |>
def MP_fence2 := <| W x=0; W y=0; W x=1; W y=1 ||  R y; Fence; R x |>
def MP_fence := <| W x=0; W y=0; W x=1; Fence; W y=1 ||  R y; Fence; R x |>

-- def x86 := [MP,MP_fence1,MP_fence2,MP_fence]
def x86 := [MP] -- ,MP_fence1,MP_fence2,MP_fence]

-- I should automate this somehow...
theorem sublist01 : List.sublist [0] (List.range 2) := by simp
theorem sublist12 : List.sublist [1] (List.range 2) := by simp

theorem sublist04 : List.sublist [0] (List.range 4) := by simp
theorem sublist14 : List.sublist [1] (List.range 4) := by simp
theorem sublist24 : List.sublist [2] (List.range 4) := by simp
theorem sublist34 : List.sublist [3] (List.range 4) := by simp

open ListTree in
def scopes_2 : ListTree ThreadId (List.range 2) :=  parentCons (ListTree.leaf [1]) (parentCons (ListTree.leaf [0]) (parentNil [0,1]) sublist01) sublist12

-- this is horrible syntax! should improve
notation "leaf" "#" n "#" => ListTree.leaf [n]
notation "parent" "#" l "#" => ListTree.parentNil l
notation  l₁ ":#" pr "#:" l₂ => ListTree.parentCons l₁ l₂ pr


open ListTree in
def scopes_4 : ListTree ThreadId (List.range 4) :=
  leaf#0# :#sublist04#: (leaf#1# :#sublist14#: (leaf#2# :#sublist24#: (leaf#3# :#sublist34#: parent # [0,1,2,3] #  )))

def valid_scopes_2 : ValidScopes := { system_scope := List.range 2, scopes := scopes_2, threads_in := sorry}
def valid_scopes_4 : ValidScopes := { system_scope := List.range 4, scopes := scopes_4, threads_in := sorry}


def tso_reorder : Request → Request → Bool
| r₁, r₂ => if r₁.isBarrier || r₂.isBarrier
then false
else
let sc_per_loc := r₁.address? == r₂.address? && r₁.address? != none
let ppo := (r₁.thread != r₂.thread) || (r₂.isWrite && r₁.isRead)
sc_per_loc || ppo
-- TODO: satisfied but not deleted?
def tso_2_sys : System := { scopes := valid_scopes_2, reorder_condition := tso_reorder}
def tso_4_sys : System := { scopes := valid_scopes_4, reorder_condition := tso_reorder}

def inittso_2 : SystemState := SystemState.init tso_2_sys
def inittso_4 : SystemState := SystemState.init tso_4_sys

-- #eval inittso_2.initZeroes [0,1,2]

end Litmus