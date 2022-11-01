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

deflitmus IRIW_one_tso_read_fence_rest_ptx := {| W. sys_rel x=1 ||  R x // 1; R y // 0 || R. sys_acq y // 1; Fence. sys_sc; R. sys_acq x // 0 || W. sys_rel y=1 |}
  where sys := { {T0, T2, T3}. PTX, {T1}. x86}

deflitmus IRIW_one_tso_read_fence_rest_ptx_rlx := {| W x=1 ||  R x // 1; R y // 0 || R y // 1; Fence. sys_sc; R x // 0 || W y=1 |}
  where sys := { {T0, T2, T3}. PTX, {T1}. x86}

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

deflitmus WRC_ptx_reader_dep := {| W x=1 || R x // 1; W y = 1 || R y // 1 ;dep R x // 0|}
  where sys := { {T0, T1}. x86, {T2}. PTX} ✓ -- TODO: This would probably be disallowed in the operational model

deflitmus WRC_ptx_reader_acq := {| W x=1 || R x // 1; W y = 1 || R. sys_acq y // 1 ; R x // 0|}
  where sys := { {T0, T1}. x86, {T2}. PTX} 𐄂

deflitmus WRC_middle_tso_dep := {| W x=1 || R x // 1; W y = 1 || R y // 1 ;dep R x // 0|}
  where sys := { {T1}. x86, {T0, T2}. PTX} ✓ -- TODO: This would probably be disallowed in the operational model

deflitmus WRC_middle_tso_acq := {| W x=1 || R x // 1; W y = 1 || R. sys_acq y // 1 ;R x // 0|}
  where sys := { {T1}. x86, {T0, T2}. PTX} 𐄂

deflitmus WRC_middle_ptx_acqrel := {| W x=1 || R. sys_acq x // 1; W. sys_rel y = 1 || R y // 1 ;R x // 0|}
  where sys := { {T1}. PTX, {T0, T2}. x86} 𐄂

deflitmus WRC_middle_ptx_acqrel_cta := {| W x=1 || R. cta_acq x // 1; W. cta_rel y = 1 || R y // 1 ;R x // 0|}
  where sys := { {T1}. PTX, {T0, T2}. x86} ✓

deflitmus WRC_middle_ptx_acqrel_fence := {| W x=1 || R x // 1; Fence. sys_acqrel; W y = 1 || R y // 1 ;R x // 0|}
  where sys := { {T1}. PTX, {T0, T2}. x86} 𐄂

deflitmus WRC_middle_ptx_acqrel_cta_fence := {| W x=1 || R x // 1; Fence. cta_acqrel; W y = 1 || R y // 1 ;R x // 0|}
  where sys := { {T1}. PTX, {T0, T2}. x86} ✓

deflitmus ISA2_right_ptx := {| W x=1;  W y=1 || R y // 1; W z = 1 || R z // 1 ; R x // 0|}
  where sys := { {T0, T1}. x86, {T2}. PTX} ✓

deflitmus ISA2_right_ptx_acq := {| W x=1;  W y=1 || R y // 1; W z = 1 || R. sys_acq z // 1 ; R x // 0|}
  where sys := { {T0, T1}. x86, {T2}. PTX} 𐄂

deflitmus ISA2_right_ptx_acq_cta := {| W x=1;  W y=1 || R y // 1; W z = 1 || R. cta_acq z // 1 ; R x // 0|}
  where sys := { {T0, T1}. x86, {T2}. PTX} ✓

deflitmus ISA2_middle_ptx := {| W x=1;  W y=1 || R y // 1; W z = 1 || R z // 1 ; R x // 0|}
  where sys := { {T0, T2}. x86, {T1}. PTX} ✓

deflitmus ISA2_middle_ptx_acqrel := {| W x=1;  W y=1 || R. sys_acq y // 1; W. sys_rel z = 1 || R z // 1 ; R x // 0|}
  where sys := { {T0, T2}. x86, {T1}. PTX} 𐄂

deflitmus ISA2_middle_ptx_acqrel_fence := {| W x=1;  W y=1 || R y // 1; Fence. sys_acqrel; W z = 1 || R z // 1 ; R x // 0|}
  where sys := { {T0, T2}. x86, {T1}. PTX} 𐄂

deflitmus ISA2_middle_ptx_acq_fence := {| W x=1;  W y=1 || R y // 1; Fence. sys_acq; W z = 1 || R z // 1 ; R x // 0|}
  where sys := { {T0, T2}. x86, {T1}. PTX} 𐄂 -- TODO: discuss this one with others; I think this should be allowed axiomatically too.

deflitmus ISA2_middle_ptx_rel_fence := {| W x=1;  W y=1 || R y // 1; Fence. sys_rel; W z = 1 || R z // 1 ; R x // 0|}
  where sys := { {T0, T2}. x86, {T1}. PTX} ✓

deflitmus dekkers_tso := {| W x=1; R y //0 || W y=1; R x // 0 |}
  where sys := { {T0, T1}. x86} 𐄂 -- this should be allowed!

deflitmus dekkers_tso_fence := {| W x=1; Fence; R y //0 || W y=1; Fence; R x // 0 |}
  where sys := { {T0, T1}. x86} 𐄂

deflitmus dekkers_ptx := {| W x=1; R y //0 || W y=1; R x // 0 |}
  where sys := { {T0, T1}. PTX} ✓

deflitmus dekkers_ptx_fence := {| W x=1; Fence; R y //0 || W y=1; Fence; R x // 0 |}
  where sys := { {T0, T1}. PTX}  𐄂

deflitmus dekkers_mix := {| W x=1; R y //0 || W y=1; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} ✓

deflitmus dekkers_mix_fence := {| W x=1; Fence; R y //0 || W y=1; Fence; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} 𐄂

deflitmus dekkers_mix_only_tso_fence := {| W x=1; R y //0 || W y=1; Fence; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} ✓

deflitmus dekkers_mix_only_ptx_fence := {| W x=1; Fence; R y //0 || W y=1; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} 𐄂

deflitmus dekkers_mix_only_cta_fence := {| W x=1; Fence. cta_sc; R y //0 || W y=1; Fence; R x // 0 |}
  where sys := { {T0}. PTX, {T1}. x86} ✓

def allTests : List Litmus.Test := litmusTests!
def tests_2 := allTests.filter λ lit => lit.numThreads == 2
def tests_3 := allTests.filter λ lit => lit.numThreads == 3
def tests_4 := allTests.filter λ lit => lit.numThreads == 4

end Litmus
end Compound
