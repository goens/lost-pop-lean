import Pop.Arch.Compound
import Litmus.CompoundTraces
namespace Compound
namespace Litmus

deflitmus IRIW_tso := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. x86} 𐄂

deflitmus IRIW_ptx := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. PTX} ✓

deflitmus IRIW_tso_reads_ptx_writes := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T3}. PTX, {T1, T2}. x86} 𐄂

deflitmus IRIW_ptx_reads_tso_writes := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T3}. x86, {T1}. PTX, {T2}. PTX} ✓

deflitmus IRIW_tso_one_read_ptx_writes := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0}. PTX, {T1}. PTX, {T3}. PTX, {T2}. x86} ✓

deflitmus IRIW_tso_fences := {| W x=1 ||  R x // 1 ; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. x86} 𐄂

deflitmus IRIW_ptx_fences := {| W x=1 ||  R x // 1 ; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. PTX} 𐄂

deflitmus IRIW_ptx_reads_tso_writes_fences := {| W x=1 ||  R x // 1 ; Fence;  R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T3}. x86, {T1}. PTX, {T2}. x86} 𐄂

deflitmus IRIW_tso_left_ptx_right := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T1}. x86, {T2, T3}. PTX} ✓

deflitmus IRIW_tso_left_ptx_right_fence := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T1}. x86, {T2, T3}. PTX} 𐄂

deflitmus IRIW_tso_left_ptx_right_fenceacqrel := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; Fence. sys_acqrel; R x // 0 || W y=1 |}
  where sys := { {T0, T1}. x86, {T2, T3}. PTX} ✓

deflitmus IRIW_tso_fence_left_ptx_right_fenceacqrel := {| W x=1 ||  R x // 1 ; Fence; R y // 0 || R y // 1; Fence. sys_acqrel; R x // 0 || W y=1 |}
  where sys := { {T0, T1}. x86, {T2, T3}. PTX} ✓

deflitmus MP_tso := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0, T1}. x86} 𐄂

deflitmus MP_ptx := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0, T1}. PTX} ✓

deflitmus MP_writes_tso := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. x86, {T1}. PTX} ✓

deflitmus MP_writes_ptx := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} ✓

deflitmus MP_writes_tso_ptx_acq_sys := {|  W x=1; W y=1 ||  R. sys_acq y // 1; R x // 0 |}
  where sys := { {T0}. x86, {T1}. PTX} 𐄂

deflitmus MP_writes_tso_ptx_acq_cta := {|  W x=1; W y=1 ||  R. cta_acq y // 1; R x // 0 |}
  where sys := { {T0}. x86, {T1}. PTX} ✓

deflitmus MP_writes_tso_ptx_acq_sys_fence := {|  W x=1; W y=1 ||  R y // 1; Fence. sys_acq; R x // 0 |}
  where sys := { {T0}. x86, {T1}. PTX} 𐄂

deflitmus MP_writes_tso_ptx_acq_cta_fence := {|  W x=1; W y=1 ||  R y // 1; Fence. cta_acq; R x // 0 |}
  where sys := { {T0}. x86, {T1}. PTX} ✓

deflitmus MP_writes_ptx_rel_sys := {|  W x=1; W. sys_rel y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} 𐄂

deflitmus MP_writes_ptx_rel_cta := {|  W x=1; W. cta_rel y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} ✓

deflitmus MP_writes_ptx_rel_sys_fence := {|  W x=1; Fence. sys_rel; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} 𐄂

deflitmus MP_writes_ptx_rel_cta_fence := {|  W x=1; Fence. cta_rel; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} ✓

def allTests : List Litmus.Test := litmusTests!
def tests_2 := allTests.filter λ lit => lit.numThreads == 2
def tests_3 := allTests.filter λ lit => lit.numThreads == 3
def tests_4 := allTests.filter λ lit => lit.numThreads == 4

end Litmus
end Compound
