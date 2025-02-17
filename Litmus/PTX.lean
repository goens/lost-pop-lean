import Pop.Arch.PTX
namespace PTX
namespace Litmus

deflitmus MP_fence_rel_acq := W.cta_rlx x=1; Fence.sys_rel; W y=1 || R y // 1; Fence.sys_acq; R x // 0
 where sys := {{T0}, {T1}}

deflitmus ISA2_mixed_scoped := W x=1; W.cta_rel y=1 || R.cta_acq y // 1; W.sys_rel z = 1 || R.sys_acq z // 1 ; R x // 0
 where sys := { {T0, T1}, {T2}}

deflitmus ISA2_mixed_scoped_cta_last := W x=1; W.cta_rel y=1 || R.cta_acq y // 1; W.sys_rel z = 1 || R.sys_acq z // 1 ; R.cta_rlx x // 0
 where sys := { {T0, T1}, {T2}}

 deflitmus WRC_mixed_cta_2_1_acqrel := W.cta_rlx x=1 || R.cta_rlx x // 1; Fence.sys_acqrel; W.sys_rlx y = 1 || R.sys_rlx y // 1 ; Fence.sys_acq; R.sys_rlx x // 0
 where sys := { {T0, T1}, {T2}} expect 𐄂

deflitmus new_mixed_scoped_cta_last := W x=1; W.cta_rel y=1 || R.cta_acq y // 1; W.sys_rel z = 1 || R.sys_acq z // 1 ; R.cta_rlx x // 0
 where sys := { {T0, T1}, {T2}}

-- Disallowed in LOST-POP PTX: the write Y can't propagate until X has propagated globally
deflitmus vijay1 := W.sys_rel X = 1; W.sys_rel Y = 1 || R.sys_acq Y // 1; R.sys_acq Z // 0 || W.sys_rel Z = 1; W.sys_rel A = 1 || R.sys_acq A // 1; R.sys_acq X // 0

deflitmus vijay2 := W.sys_rel X = 1; W.sys_rel Y = 1 || R.sys_acq Y // 1; W.sys_rel Z = 1; R Z // 2 || W.sys_rel Z = 2; W.sys_rel A = 1 || R.sys_acq A // 1; R.sys_acq X // 0

def allTests : List Litmus.Test := litmusTests!

end Litmus
end PTX
