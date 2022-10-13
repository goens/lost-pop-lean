import Pop.Arch.PTX
namespace Litmus

deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |} ✓
deflitmus IRIW_3ctas := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } 𐄂
deflitmus IRIW_4ctas := {| W x=1 ||  R. cta_rlx x // 1 ; Fence. sys_sc;  R. cta_rlx y // 0 || R. cta_rlx y // 1; Fence. sys_sc; R. sys_rlx x // 0 || W y=1 |}
  where sys := { {T0}, {T1}, {T2}, {T3} } ✓
deflitmus IRIW_3ctas_1scoped_w := {| W. cta_rlx x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ✓
deflitmus IRIW_3ctas_1scoped_r := {| W x=1 ||  R. cta_rlx x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } ✓
deflitmus IRIW_3ctas_scoped_rs_after := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R. cta_rlx y // 0 || R y // 1; Fence. cta_sc; R. cta_rlx x // 0 || W y=1 |}
  where sys := { {T0}, {T1, T2}, {T3} } 𐄂
deflitmus IRIW_2ctas := {| W x=1 ||  R x // 1 ; Fence. cta_sc;  R y // 0 || R y // 1; Fence. cta_sc; R x // 0 || W y=1 |}
  where sys := { {T0, T2}, {T1, T3} } ✓
deflitmus IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |} 𐄂
deflitmus IRIW_sc_acq_fence := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence. sys_acqrel; R x // 0 || W y=1 |} ✓
deflitmus simpleRF := {| W. cta_rlx x=1 || R. cta_rlx x // 1 |}
  where sys := { {T0}, {T1} } ✓
Trace Hint := [Accept (R. cta_rlx x) at Thread 1, Accept (W. cta_rlx x = 1) at Thread 0, Propagate Request 2 to Thread 1, Propagate Request 1 to Thread 0, Satisfy Request 1 with Request 2]
deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |} ✓
  Trace Hint := [Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 5]
deflitmus MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |} ✓
  Trace Hint := [Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 3 to Thread 0, Accept (Fence. sys_sc) at Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Accept (W y = 1) at Thread 0, Propagate Request 6 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 6]
deflitmus MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |} ✓
  Trace Hint := [Accept (R y) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 4 to Thread 1, Accept (Fence. sys_sc) at Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 4, Propagate Request 5 to Thread 0, Accept (R x) at Thread 1, Propagate Request 6 to Thread 0, Satisfy Request 6 with Request 0, Propagate Request 3 to Thread 1]
deflitmus MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|} 𐄂
deflitmus MP_fence_cta := {| W x=1; Fence. cta_sc; W y=1 ||  R y // 1; Fence. cta_sc; R x // 0|}
  where sys := { {T0}, {T1} } ✓
  Trace Hint := [Accept (R y) at Thread 1, Accept (Fence. cta_sc) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. cta_sc) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1, Propagate Request 6 to Thread 1, Propagate Request 7 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 7]
deflitmus MP_read_cta := {| W x=1; Fence. sys_sc; W y=1 ||  R. cta_rlx y // 1; Fence. sys_sc; R x // 0|}
  where sys := { {T0}. ptx, {T1}. x86} 𐄂
deflitmus MP_fence_consumer_weak := {| W. sys_weak x=1; Fence. sys_sc; W y=1 ||  R y // 1; Fence. sys_sc; R. sys_weak x // 0|} -- 𐄂
deflitmus MP_fence_weak := {| W. sys_weak x=1; Fence. sys_sc; W. sys_weak y=1 ||  R. sys_weak y // 1; Fence. sys_sc; R. sys_weak x // 0|} -- 𐄂
deflitmus MP_fence_weak_rel_acq := {| W. sys_weak x=1; Fence. sys_rel; W. sys_weak y=1 ||  R. sys_weak y // 1; Fence. sys_acq; R. sys_weak x // 0|} -- 𐄂
deflitmus MP_fence_rel_acq := {| W x=1; Fence. sys_rel; W  y=1 ||  R y // 1; Fence. sys_acq; R x // 0|} 𐄂 --
deflitmus MP_rel_acq := {| W x=1; W. sys_rel y=1 ||  R. sys_acq y // 1; R x // 0|} 𐄂
deflitmus MP_fence_cta_1fence := {| W x=1; Fence. sys_sc; W y=1 ||  R y // 1; Fence. cta_sc; R x // 0|}
  where sys := { {T0}, {T1} } ✓
  Trace Hint := [Accept (R y) at Thread 1, Accept (Fence. cta_sc) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 0, Accept (Fence. sys_sc) at Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1, Propagate Request 6 to Thread 1, Accept (W y = 1) at Thread 0, Propagate Request 7 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 7 ]

deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |} ✓
  Trace Hint := [Accept (W y = 1) at Thread 1, Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 0, Accept (R y) at Thread 0, Satisfy Request 3 with Request 2, Satisfy Request 6 with Request 5, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 1, Propagate Request 2 to Thread 0]
deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |}  ✓
  Trace Hint := [Accept (W y = 1) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R y) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Satisfy Request 5 with Request 1, Propagate Request 2 to Thread 0]
deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |} 𐄂
deflitmus dekkers_acqrelfence := {| W x=1; Fence. sys_acqrel; R y //0 || W y=1; Fence. sys_acqrel;  R x // 0 |} ✓
deflitmus WRC := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|} ✓
   Trace Hint := [Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 3, Accept (W y = 1) at Thread 1, Propagate Request 5 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 5 to Thread 2, Satisfy Request 2 with Request 5, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]
deflitmus WRC_two_deps := {| W x=1 || R. sys_acq x // 1;dep W y = 1 || R y // 1 ;dep R x // 0|} ✓
  Trace Hint := [Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 3, Accept (W y = 1) at Thread 1, Propagate Request 5 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 5 to Thread 2, Satisfy Request 2 with Request 5, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]
deflitmus WRC_rel := {| W. sys_rel x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|} ✓   Trace Hint := [Accept (R y) at Thread 2, Accept (W. sys_rel x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 3 to Thread 1, Propagate Request 2 to Thread 0, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 3, Accept (W y = 1) at Thread 1, Propagate Request 5 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 5 to Thread 2, Satisfy Request 2 with Request 5, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]
deflitmus WRC_acq := {| W x=1 || R. sys_acq x // 1; W y = 1 || R. sys_acq y // 1 ;dep R x // 0|} ✓
   Trace Hint := [Accept (W x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 2 to Thread 1, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 2, Accept (W y = 1) at Thread 1, Accept (R. sys_acq y) at Thread 2, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 2, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 1, Satisfy Request 5 with Request 4, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 2 to Thread 2, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]
deflitmus WRC_no_dep := {| W x=1 || R. sys_acq x // 1; W y = 1 || R y // 1 ; R x // 0|} ✓
  Trace Hint := [Accept (R y) at Thread 2, Accept (R x) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 4 to Thread 2, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Accept (W y = 1) at Thread 1, Satisfy Request 5 with Request 4, Propagate Request 6 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 6 to Thread 2, Satisfy Request 2 with Request 6]
deflitmus WRC_cta_1_2 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0}, {T1, T2}} 𐄂
  Trace Hint := [Accept (R. cta_rlx y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Accept (R x) at Thread 2, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Accept (R x) at Thread 1, Accept (Fence. sys_rel) at Thread 1, Accept (W. cta_rlx y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 2, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Satisfy Request 2 with Request 7, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Propagate Request 6 to Thread 0, Propagate Request 8 to Thread 2, Satisfy Request 5 with Request 8]
deflitmus WRC_cta_1_2_acqrel := {| W x=1 || R. sys_rlx x // 1; Fence. sys_acqrel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acqrel; R. sys_rlx x // 0 |}
  where sys := { {T0}, {T1, T2}} 𐄂
  Trace Hint := [Accept (R. cta_rlx y) at Thread 2, Accept (Fence. sys_acqrel) at Thread 2, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Accept (R x) at Thread 2, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_acqrel) at Thread 1, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 2, Propagate Request 6 to Thread 1, Propagate Request 5 to Thread 0, Accept (W. cta_rlx y = 1) at Thread 1, Propagate Request 6 to Thread 2, Satisfy Request 5 with Request 6, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 8 to Thread 0, Propagate Request 8 to Thread 2, Satisfy Request 2 with Request 8]
deflitmus WRC_cta_2_1 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0, T1}, {T2}} ✓
  Trace Hint := [Accept (R. cta_rlx y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Accept (R x) at Thread 2, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Accept (R x) at Thread 1, Accept (Fence. sys_rel) at Thread 1, Accept (W. cta_rlx y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Satisfy Request 2 with Request 7, Propagate Request 8 to Thread 1, Propagate Request 8 to Thread 2, Satisfy Request 5 with Request 8]
deflitmus WRC_cta_2_1' := {| W. cta_rlx x=1 || R. cta_rlx x // 1; Fence. sys_rel; W. sys_rlx y = 1 || R. sys_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0, T1}, {T2}} 𐄂
deflitmus WRC_cta_1_1_1 := {| W x=1 || R. sys_rlx x // 1; Fence. sys_rel; W. cta_rlx y = 1 || R. cta_rlx y // 1 ; Fence. sys_acq; R. sys_rlx x // 0 |}
  where sys := { {T0}, {T1}, {T2}} ✓
   Trace Hint := [Accept (R. cta_rlx y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Accept (R x) at Thread 2, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Accept (R x) at Thread 1, Accept (Fence. sys_rel) at Thread 1, Accept (W. cta_rlx y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 2, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Satisfy Request 2 with Request 7, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Propagate Request 6 to Thread 0, Propagate Request 8 to Thread 2, Satisfy Request 5 with Request 8]
deflitmus WWRWRR := {| W. cta_rel x=1;  W. cta_rel y=1 || R. cta_acq y // 1; W. cta_rel z = 1 || R. cta_acq z // 1 ; R. cta_acq x // 0|} 𐄂

deflitmus WWRWRR_fences := {| W x=1; Fence. sys_rel; W y=1 || R y // 1; Fence. sys_acq; W z = 1 || R z // 1 ; Fence. sys_acq; R x // 0|} ✓
deflitmus WWRWRR_fences' := {| W x=1; Fence. sys_rel; W y=1 || R y // 1; Fence. sys_acqrel; W z = 1 || R z // 1 ; Fence. sys_acq; R x // 0|} 𐄂
deflitmus WWRWRR_scoped := {| W. cta_rel x=1;  W. cta_rel y=1 || R. cta_acq y // 1; W. cta_rel z = 1 || R. cta_acq z // 1 ; R. cta_acq x // 0|}
  where sys := { {T0}, {T1, T2}} 𐄂
deflitmus three_vars_ws := {| W x = 1; Fence. sys_acqrel; W y = 1 || W y = 2; Fence. sys_acqrel; W z = 1 || R z // 1; Fence. sys_acqrel; R x // 0 |} ✓
deflitmus two_plus_two2 := {| W. sys_rel x=1; W. sys_rel y=2;  R. sys_acq y // 1 || W. sys_rel y=1; W. sys_rel x=2 ;  R. sys_acq x // 1|} ✓
deflitmus co_two_thread := {| W x = 1; R x // 2 || W x = 2; R x // 1 |} ✓
deflitmus co_four_thread := {| W x = 1 || R x // 1 ; R x // 2 ||  R x // 2; R x // 1; W x = 2 |} 𐄂
deflitmus write_serialization := {| W. cta_rlx x=1;  W. cta_rlx x=2 || R. cta_rlx x // 1; R. cta_rlx x // 2 || R. cta_rlx x // 2 ; R. cta_rlx x // 1|}
  where sys := { {T0, T1}, {T2} } ✓
deflitmus write_serialization_unscoped := {| W. cta_rlx x=1;  W. cta_rlx x=2 || R. cta_rlx x // 1; R. cta_rlx x // 2 || R. cta_rlx x // 2 ; R. cta_rlx x // 1|} 𐄂


def allPTX : List Litmus.Test := litmusTests!
def ptx_2 := allPTX.filter λ lit => lit.numThreads == 2
def ptx_3 := allPTX.filter λ lit => lit.numThreads == 3
def ptx_4 := allPTX.filter λ lit => lit.numThreads == 4

end Litmus
