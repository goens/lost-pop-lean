import Pop.Arch.PTX
namespace PTX
namespace Litmus

hint for IRIW := [Accept (R y) at Thread 2, Accept (R x) at Thread 2, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 0, Accept (R x) at Thread 1, Accept (R y) at Thread 1, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 5 to Thread 3, Satisfy Request 5 with Request 1, Accept (W y = 1) at Thread 3, Accept (W x = 1) at Thread 0, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 2 to Thread 3, Satisfy Request 2 with Request 6, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3, Satisfy Request 4 with Request 7]

hint for IRIW_dep := [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 5 to Thread 1, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 5, Propagate Request 2 to Thread 2, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (R x) at Thread 2, Accept (R y) at Thread 1, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 3, Satisfy Request 6 with Request 0, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3, Satisfy Request 7 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 5 to Thread 2, Propagate Request 5 to Thread 3]

hint for IRIW_dep_sc := [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 5 to Thread 1, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 5, Propagate Request 2 to Thread 2, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (Fence. sys_dep) at Thread 1, Accept (Fence. sys_sc) at Thread 2, Accept (R x) at Thread 2, Accept (R y) at Thread 1, Propagate Request 9 to Thread 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3, Satisfy Request 9 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 8 to Thread 0, Propagate Request 8 to Thread 3, Propagate Request 8 to Thread 1, Satisfy Request 8 with Request 0, Propagate Request 5 to Thread 2, Propagate Request 5 to Thread 3]

hint for IRIW_4ctas := [Accept (W y = 1) at Thread 3, Accept (R. cta_rlx y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R. cta_rlx x) at Thread 1, Propagate Request 4 to Thread 1, Propagate Request 2 to Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 4, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (Fence. sys_sc) at Thread 2, Accept (R x) at Thread 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 3, Satisfy Request 7 with Request 0, Accept (Fence. sys_sc) at Thread 1, Accept (R. cta_rlx y) at Thread 1, Propagate Request 9 to Thread 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3, Satisfy Request 9 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3]

hint for WRC_sc_dep := [Accept (R y) at Thread 2, Accept (Fence. sys_dep) at Thread 2, Accept (R x) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. sys_sc) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 8, Propagate Request 8 to Thread 2, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 8, Propagate Request 7 to Thread 0]

hint for  IRIW_3ctas_1scoped_w  := [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (Fence. cta_sc) at Thread 2, Accept (R x) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. cta_sc) at Thread 1, Accept (R y) at Thread 1, Accept (W. cta_rlx x = 1) at Thread 0, Propagate Request 9 to Thread 1, Propagate Request 6 to Thread 0, Satisfy Request 6 with Request 9, Propagate Request 2 to Thread 2, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Propagate Request 8 to Thread 2, Propagate Request 8 to Thread 3, Propagate Request 8 to Thread 0, Satisfy Request 8 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 1, Propagate Request 5 to Thread 3, Satisfy Request 5 with Request 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3]

hint for  IRIW_3ctas_1scoped_r  := [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R. cta_rlx x) at Thread 1, Propagate Request 4 to Thread 1, Propagate Request 2 to Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 4, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (Fence. cta_sc) at Thread 2, Accept (R x) at Thread 2, Accept (Fence. cta_sc) at Thread 1, Accept (R y) at Thread 1, Propagate Request 9 to Thread 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3, Satisfy Request 9 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 3, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 0, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3]

hint for  IRIW_2ctas  := [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Propagate Request 4 to Thread 1, Propagate Request 2 to Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 4, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (Fence. cta_sc) at Thread 2, Accept (R x) at Thread 2, Accept (Fence. cta_sc) at Thread 1, Accept (R y) at Thread 1, Propagate Request 4 to Thread 3, Propagate Request 9 to Thread 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3, Satisfy Request 9 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 3, Satisfy Request 7 with Request 0, Propagate Request 4 to Thread 2]
hint for  IRIW_acq_fences:= [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Propagate Request 4 to Thread 1, Propagate Request 2 to Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 4, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 3, Satisfy Request 7 with Request 0, Accept (Fence. sys_acq) at Thread 1, Accept (R y) at Thread 1, Propagate Request 9 to Thread 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3, Satisfy Request 9 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3]
hint for  IRIW_acqrel_fences:= [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Propagate Request 4 to Thread 1, Propagate Request 2 to Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 4, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (Fence. sys_acqrel) at Thread 2, Accept (R x) at Thread 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 3, Accept (Fence. sys_acqrel) at Thread 1, Accept (R y) at Thread 1, Satisfy Request 7 with Request 0, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3, Propagate Request 9 to Thread 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3, Satisfy Request 9 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1]
hint for  IRIW_sc_acqrel_fence:= [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Propagate Request 4 to Thread 1, Propagate Request 2 to Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 4, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (Fence. sys_acqrel) at Thread 2, Accept (R x) at Thread 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 3, Accept (Fence. sys_sc) at Thread 1, Accept (R y) at Thread 1, Satisfy Request 7 with Request 0, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3, Propagate Request 9 to Thread 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3, Satisfy Request 9 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1]
hint for  simpleRF := [Accept (R. cta_rlx x) at Thread 1, Accept (W. cta_rlx x = 1) at Thread 0, Propagate Request 2 to Thread 1, Propagate Request 1 to Thread 0, Satisfy Request 1 with Request 2]
hint for  MP:= [Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 5]
hint for  MP_fence1:= [Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 3 to Thread 0, Accept (Fence. sys_sc) at Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Accept (W y = 1) at Thread 0, Propagate Request 6 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 6]
hint for  MP_fence2:= [Accept (R y) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 4 to Thread 1, Accept (Fence. sys_sc) at Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 4, Accept (R x) at Thread 1, Propagate Request 6 to Thread 0, Satisfy Request 6 with Request 0, Propagate Request 3 to Thread 1]
hint for  MP_fence_cta  := [Accept (R y) at Thread 1, Accept (Fence. cta_sc) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. cta_sc) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1, Propagate Request 7 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 7]
hint for  MP_fence_rel_acq := [Accept (R y) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_rel) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 5 to Thread 1, Accept (Fence. sys_acq) at Thread 1, Accept (R x) at Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 5, Propagate Request 7 to Thread 0, Satisfy Request 7 with Request 0, Propagate Request 3 to Thread 1]
hint for  MP_fence_cta_1fence  := [Accept (R y) at Thread 1, Accept (Fence. cta_sc) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_sc) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1, Propagate Request 7 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 7]

hint for  N7:= [Accept (W y = 1) at Thread 1, Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 0, Accept (R y) at Thread 0, Satisfy Request 3 with Request 2, Satisfy Request 6 with Request 5, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 1, Propagate Request 2 to Thread 0]
hint for  dekkers:= [Accept (W y = 1) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R y) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Satisfy Request 5 with Request 1, Propagate Request 2 to Thread 0]
hint for  dekkers_acqrel:= [Accept (W. sys_rel y = 1) at Thread 1, Accept (R. sys_acq x) at Thread 1, Accept (W. sys_rel x = 1) at Thread 0, Accept (R. sys_acq y) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Satisfy Request 5 with Request 1, Propagate Request 2 to Thread 0]
hint for  dekkers_acqrelfence:= [Accept (W y = 1) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (R x) at Thread 1, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Accept (W x = 1) at Thread 0, Accept (Fence. sys_acqrel) at Thread 0, Accept (R y) at Thread 0, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 5 to Thread 1]
hint for  dekkers_relfence:= [Accept (W y = 1) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_rel) at Thread 0, Accept (R y) at Thread 0, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 1, Propagate Request 2 to Thread 0, Accept (R x) at Thread 1, Propagate Request 7 to Thread 0, Satisfy Request 7 with Request 0, Propagate Request 4 to Thread 1]
hint for  dekkers_acqfence:= [Accept (W y = 1) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_acq) at Thread 0, Accept (R x) at Thread 1, Accept (R y) at Thread 0, Propagate Request 6 to Thread 0, Satisfy Request 6 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 1, Propagate Request 2 to Thread 0]

hint for  WRC:= [Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 3, Accept (W y = 1) at Thread 1, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 5, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]
hint for  WRC_acqrel:= [Accept (R. sys_acq y) at Thread 2, Accept (W x = 1) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 1, Accept (R. sys_acq x) at Thread 2, Accept (R. sys_acq x) at Thread 1, Accept (W. sys_rel y = 1) at Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 3, Propagate Request 6 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 6 to Thread 2, Satisfy Request 2 with Request 6, Propagate Request 4 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0]

hint for  WRC_two_deps:= [Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 3, Accept (W y = 1) at Thread 1, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 5, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]
hint for  WRC_acq:= [Accept (W x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 2 to Thread 1, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 2, Accept (W y = 1) at Thread 1, Accept (R. sys_acq y) at Thread 2, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 2, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 1, Satisfy Request 5 with Request 4, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 2 to Thread 2, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]
hint for  WRC_no_dep:= [Accept (R y) at Thread 2, Accept (R x) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R. sys_acq x) at Thread 1, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 4 to Thread 2, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Accept (W y = 1) at Thread 1, Satisfy Request 5 with Request 4, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 6]
hint for  WRC_cta_1_2  := [Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R. cta_rlx y) at Thread 2, Propagate Request 3 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 3, Accept (Fence. sys_rel) at Thread 1, Accept (W. cta_rlx y = 1) at Thread 1, Propagate Request 6 to Thread 2, Propagate Request 6 to Thread 0, Propagate Request 4 to Thread 1, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 6, Propagate Request 8 to Thread 0, Propagate Request 8 to Thread 1, Satisfy Request 8 with Request 0]
hint for  WRC_cta_1_2_acqrel  := [Accept (R. cta_rlx y) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. sys_acqrel) at Thread 2, Accept (W x = 1) at Thread 0, Accept (Fence. sys_acqrel) at Thread 1, Propagate Request 2 to Thread 0, Propagate Request 5 to Thread 1, Accept (W. cta_rlx y = 1) at Thread 1, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 5, Propagate Request 6 to Thread 2, Propagate Request 6 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Propagate Request 7 to Thread 0, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Accept (R x) at Thread 2, Propagate Request 8 to Thread 0, Satisfy Request 2 with Request 7, Propagate Request 5 to Thread 2, Propagate Request 8 to Thread 1, Satisfy Request 8 with Request 0]
hint for  WRC_cta_2_1  := [Accept (R. cta_rlx y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. sys_rel) at Thread 1, Accept (R x) at Thread 2, Accept (W. cta_rlx y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 4 to Thread 2, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0, Propagate Request 8 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 8 to Thread 2, Satisfy Request 4 with Request 8, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7]
hint for  WRC_cta_2_1' := [Accept (W. cta_rlx x = 1) at Thread 0, Accept (R y) at Thread 2, Propagate Request 2 to Thread 1, Accept (Fence. sys_acq) at Thread 2, Accept (R. cta_rlx x) at Thread 1, Accept (R x) at Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 2, Accept (Fence. sys_rel) at Thread 1, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Accept (W y = 1) at Thread 1, Propagate Request 8 to Thread 2, Propagate Request 3 to Thread 1, Satisfy Request 3 with Request 8, Propagate Request 4 to Thread 1, Propagate Request 8 to Thread 0, Propagate Request 4 to Thread 0, Propagate Request 6 to Thread 0, Propagate Request 2 to Thread 2, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]
hint for  WRC_rel_mid:= [Accept (R y) at Thread 2, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_acq) at Thread 2, Accept (Fence. sys_rel) at Thread 1, Propagate Request 3 to Thread 2, Propagate Request 4 to Thread 1, Propagate Request 3 to Thread 0, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Accept (W y = 1) at Thread 1, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 0, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 1, Accept (R x) at Thread 2, Propagate Request 8 to Thread 0, Propagate Request 8 to Thread 1, Satisfy Request 8 with Request 0, Propagate Request 4 to Thread 2, Satisfy Request 3 with Request 4]
hint for  WRC_rel_mid_no_fence:= [Accept (R y) at Thread 2, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_acq) at Thread 2, Accept (W. sys_rel y = 1) at Thread 1, Propagate Request 2 to Thread 0, Accept (R x) at Thread 2, Propagate Request 4 to Thread 1, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 4, Propagate Request 6 to Thread 2, Propagate Request 2 to Thread 1, Propagate Request 6 to Thread 0, Satisfy Request 2 with Request 6, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 1, Propagate Request 7 to Thread 0, Propagate Request 4 to Thread 2, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 0]
hint for  WRC_acq_mid:= [Accept (R y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Accept (R. sys_acq x) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 7 to Thread 1, Propagate Request 5 to Thread 0, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 6, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 7 to Thread 2, Satisfy Request 5 with Request 7]

hint for  WRC_cta_2_1_acqrel :=  [Accept (R y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Accept (W. cta_rlx x = 1) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 5 to Thread 1, Accept (R. cta_rlx x) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (W y = 1) at Thread 1, Propagate Request 6 to Thread 0, Satisfy Request 6 with Request 5, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 8 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 8 to Thread 2, Satisfy Request 2 with Request 8, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 2]

hint for  WRC_cta_1_1_1  := [Accept (R. cta_rlx y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (W. cta_rlx y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 2, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Propagate Request 8 to Thread 2, Satisfy Request 5 with Request 8, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7]
hint for  WRC_cta_1_1_1' := [Accept (R y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Accept (R. cta_rlx x) at Thread 1, Accept (Fence. sys_rel) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 8, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 8 to Thread 2]

hint for  MP3:= [Accept (R z) at Thread 2, Accept (R x) at Thread 2, Accept (R y) at Thread 1, Accept (W z = 1) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 6 to Thread 2, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 1, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 2, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Propagate Request 6 to Thread 0, Propagate Request 8 to Thread 2, Satisfy Request 3 with Request 6, Satisfy Request 4 with Request 0, Satisfy Request 5 with Request 8]
hint for  MP3_acqrel:= [Accept (R. cta_acq z) at Thread 2, Accept (R. cta_acq x) at Thread 2, Accept (R. cta_acq y) at Thread 1, Accept (W. cta_rel z = 1) at Thread 1, Accept (W. cta_rel x = 1) at Thread 0, Accept (W. cta_rel y = 1) at Thread 0, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 6 to Thread 2, Propagate Request 3 to Thread 1, Propagate Request 4 to Thread 1, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 2, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Propagate Request 6 to Thread 0, Propagate Request 8 to Thread 2, Satisfy Request 3 with Request 6, Satisfy Request 4 with Request 0, Satisfy Request 5 with Request 8]
hint for  MP3_fences := [Accept (R z) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R y) at Thread 1, Accept (Fence. sys_acq) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_rel) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 7 to Thread 1, Propagate Request 8 to Thread 1, Propagate Request 9 to Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 9, Accept (W z = 1) at Thread 1, Propagate Request 10 to Thread 2, Propagate Request 3 to Thread 1, Satisfy Request 3 with Request 10, Accept (R x) at Thread 2, Propagate Request 11 to Thread 0, Propagate Request 11 to Thread 1, Satisfy Request 11 with Request 0, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 2, Propagate Request 8 to Thread 2, Propagate Request 9 to Thread 2, Propagate Request 10 to Thread 0]
hint for  MP3_fences_rel := [Accept (R z) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R y) at Thread 1, Accept (Fence. sys_acq) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_rel) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 7 to Thread 1, Propagate Request 8 to Thread 1, Propagate Request 9 to Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 9, Accept (W z = 1) at Thread 1, Propagate Request 10 to Thread 2, Propagate Request 3 to Thread 1, Satisfy Request 3 with Request 10, Accept (R x) at Thread 2, Propagate Request 11 to Thread 0, Propagate Request 11 to Thread 1, Satisfy Request 11 with Request 0, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 2, Propagate Request 8 to Thread 2, Propagate Request 9 to Thread 2, Propagate Request 10 to Thread 0]
hint for  MP3_scoped  := [Accept (R. cta_acq z) at Thread 2, Accept (R. cta_acq y) at Thread 1, Accept (W. cta_rel x = 1) at Thread 0, Accept (W. cta_rel y = 1) at Thread 0, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 2, Accept (W. cta_rel z = 1) at Thread 1, Propagate Request 5 to Thread 1, Propagate Request 6 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 6 to Thread 2, Satisfy Request 4 with Request 6, Propagate Request 7 to Thread 0, Accept (R. cta_acq x) at Thread 2, Propagate Request 7 to Thread 2, Propagate Request 3 to Thread 1, Satisfy Request 3 with Request 7, Propagate Request 8 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 8 to Thread 1, Satisfy Request 8 with Request 0]
hint for  three_vars_ws:= [Accept (R z) at Thread 2, Accept (Fence. sys_acqrel) at Thread 2, Accept (R x) at Thread 2, Accept (W y = 2) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (W z = 1) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence. sys_acqrel) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Propagate Request 8 to Thread 0, Propagate Request 8 to Thread 2, Propagate Request 3 to Thread 1, Satisfy Request 3 with Request 8, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 1, Satisfy Request 5 with Request 0, Propagate Request 9 to Thread 1, Propagate Request 9 to Thread 2, Propagate Request 11 to Thread 1, Propagate Request 11 to Thread 2]
hint for  two_plus_two2:= [Accept (W. sys_rel y = 1) at Thread 1, Accept (W. sys_rel x = 2) at Thread 1, Accept (W. sys_rel x = 1) at Thread 0, Accept (W. sys_rel y = 2) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Accept (R. sys_acq x) at Thread 1, Accept (R. sys_acq y) at Thread 0, Propagate Request 6 to Thread 0, Satisfy Request 6 with Request 4, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 2]
hint for  simple_write_serialization_extra_thread := [Accept (W y = 1) at Thread 2, Accept (R y) at Thread 2, Accept (R x) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W x = 2) at Thread 0, Satisfy Request 3 with Request 2, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 4 to Thread 2, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 2, Propagate Request 4 to Thread 0, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 7 to Thread 1, Satisfy Request 4 with Request 7, Satisfy Request 5 with Request 6]
hint for  write_serialization  := [Accept (R. cta_rlx x) at Thread 2, Accept (R. cta_rlx x) at Thread 2, Accept (R. cta_rlx x) at Thread 1, Accept (R. cta_rlx x) at Thread 1, Accept (W. cta_rlx x = 1) at Thread 0, Accept (W. cta_rlx x = 2) at Thread 0, Propagate Request 1 to Thread 1, Propagate Request 3 to Thread 2, Propagate Request 5 to Thread 1, Propagate Request 5 to Thread 2, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 5, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 5, Propagate Request 4 to Thread 2, Propagate Request 6 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 6 to Thread 2, Satisfy Request 4 with Request 6, Propagate Request 1 to Thread 0, Satisfy Request 1 with Request 6]

hint for write_serialization_unscoped := [Accept (R. cta_rlx x) at Thread 2, Accept (R. cta_rlx x) at Thread 2, Accept (R. cta_rlx x) at Thread 1, Accept (R. cta_rlx x) at Thread 1, Accept (W. cta_rlx x = 1) at Thread 0, Accept (W. cta_rlx x = 2) at Thread 0, Propagate Request 5 to Thread 2, Propagate Request 5 to Thread 1, Propagate Request 3 to Thread 0, Propagate Request 1 to Thread 1, Propagate Request 3 to Thread 2, Satisfy Request 3 with Request 5, Propagate Request 4 to Thread 2, Propagate Request 6 to Thread 1, Propagate Request 1 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 5, Propagate Request 6 to Thread 2, Satisfy Request 1 with Request 6, Satisfy Request 4 with Request 6]

hint for WRC_rel_first := [Accept (R y) at Thread 2, Accept (R. sys_acq x) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W. sys_rel x = 1) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 5 to Thread 1, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 4, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 5 to Thread 2, Satisfy Request 3 with Request 5, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0]

hint for two_plus_two2_rlx := [Accept (W y = 1) at Thread 1, Accept (W x = 2) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 2) at Thread 0, Accept (R y) at Thread 0, Propagate Request 3 to Thread 0, Propagate Request 5 to Thread 1, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 5, Propagate Request 6 to Thread 1, Propagate Request 2 to Thread 0, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 2]

hint for IRIW_relacq := [Accept (W. sys_rel y = 1) at Thread 3, Accept (R. sys_acq y) at Thread 2, Accept (R. sys_acq x) at Thread 2, Accept (R. sys_acq x) at Thread 1, Accept (R. sys_acq y) at Thread 1, Accept (W. sys_rel x = 1) at Thread 0, Propagate Request 7 to Thread 1, Propagate Request 2 to Thread 2, Propagate Request 3 to Thread 3, Propagate Request 5 to Thread 0, Satisfy Request 3 with Request 2, Satisfy Request 5 with Request 7, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Propagate Request 4 to Thread 3, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Propagate Request 6 to Thread 3, Satisfy Request 4 with Request 0, Satisfy Request 6 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3]

hint for WRC_cta_1_1_1_rf_cta_left := [Accept (R y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Accept (R. cta_rlx x) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 8, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 7 to Thread 0, Propagate Request 8 to Thread 2]

hint for WRC_cta_1_1_1_cta_rf_left := [Accept (R y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W. cta_rlx x = 1) at Thread 0, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 8, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 7 to Thread 0, Propagate Request 8 to Thread 2]

hint for WRC_cta_1_1_1_cta_rf_left_sc_acq := [Accept (R y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. sys_sc) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W. cta_rlx x = 1) at Thread 0, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 8, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 7 to Thread 0, Propagate Request 8 to Thread 2]

hint for WRC_cta_1_1_1_cta_rf_left_sc := [Accept (R y) at Thread 2, Accept (Fence. sys_sc) at Thread 2, Accept (R x) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. sys_sc) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W. cta_rlx x = 1) at Thread 0, Propagate Request 8 to Thread 1, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 8, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7, Propagate Request 7 to Thread 0, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 8 to Thread 2]

hint for WRC_cta_1_1_1_cta_rf_right := [Accept (R. cta_rlx y) at Thread 2, Accept (Fence. sys_acq) at Thread 2, Accept (R x) at Thread 2, Accept (R x) at Thread 1, Accept (Fence. sys_acqrel) at Thread 1, Accept (W. cta_rlx y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 8 to Thread 1, Propagate Request 8 to Thread 2, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Satisfy Request 5 with Request 8, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 7]

end Litmus
end PTX
