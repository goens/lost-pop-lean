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
deflitmus vijay_fr_trailing := W.sys_rel X = 1; Fence; W.sys_rel Y = 1 || R.sys_acq Y // 1; R.sys_acq Z // 0 || W.sys_rel Z = 1; Fence; W.sys_rel A = 1 || R.sys_acq A // 1; R.sys_acq X // 0

deflitmus vijay_ws_trailing := W.sys_rel X = 1; Fence; W.sys_rel Y = 1 || R.sys_acq Y // 1; W.sys_rel Z = 1; R Z // 2 || W.sys_rel Z = 2; Fence; W.sys_rel A = 1 || R.sys_acq A // 1; R.sys_acq X // 0

deflitmus vijay_fr_leading := W.sys_rel X = 1; W.sys_rel Y = 1 || R.sys_acq Y // 1; Fence; R.sys_acq Z // 0 || W.sys_rel Z = 1; W.sys_rel A = 1 || R.sys_acq A // 1; Fence; R.sys_acq X // 0

deflitmus vijay_ws_leading := W.sys_rel X = 1; W.sys_rel Y = 1 || R.sys_acq Y // 1; Fence; W.sys_rel Z = 1; R Z // 2 || W.sys_rel Z = 2; W.sys_rel A = 1 || R.sys_acq A // 1; Fence; R.sys_acq X // 0

deflitmus vijay_ws_trailing_scoped := W.sys_rel X = 1; Fence; W.cta_rel Y = 1 || R.cta_acq Y // 1; W.sys_rel Z = 1; R Z // 2 || W.sys_rel Z = 2; Fence; W.cta_rel A = 1 || R.cta_acq A // 1; R.sys_acq X // 0
  where sys := { {T0, T1}, {T2, T3}}

deflitmus dennis_counterexample := W.sys_sc X = 1; R.sys_rel X // 2 || W.cta_sc Z = 2; W.sys_rel V = 1; R.sys_rlx Z // 1 || R.sys_acq V // 1; W.cta_sc X = 2  || R.sys_sc X // 1; W.cta_rel Y = 1 || R.cta_acq Y // 1 ; W.cta_sc Z = 1
  where sys := {{T0,T1,T2}, {T3,T4}}

deflitmus co := W.cta_rlx X = 1; W.cta_rlx X = 2 || R.cta_rlx X // 1; R.cta_rlx X // 2 || R.cta_rlx X // 2; R.cta_rlx X // 1
  where sys := {{T0},{T1,T2}}

deflitmus dennis_counterexample_mapping_scopes :=
  Fence.sys_sc; W.sys_rel Z = 1 ||
  Fence.cta_sc; R.cta_acq Z // 1; Fence.cta_sc; W.cta_rel X = 1; R.cta_rlx X // 2 ||
  Fence.sys_sc; W.sys_rel X = 2; W.sys_rel Y = 1 ||
  R.sys_acq Y // 1; Fence.sys_sc; R.sys_acq Z // 0
  where sys := { {T0, T1, T2}, {T3}}

deflitmus dennis_counterexample_scopes_power :=
    W.sys_rel X = 1; Fence.sys_sc; W.sys_rel Y = 1; R.sys_rlx X // 2 ||
    R.sys_acq Y // 1; W.cta_rlx Z = 1; R.cta_rlx Z // 2 ||
    W.cta_rlx Z = 2; W.sys_rel U = 1  ||
    R.sys_acq U // 1; Fence.sys_sc; W.sys_rel X = 2
    where sys := { {T0}, {T1, T2}, {T3}}

def allTests : List Litmus.Test := litmusTests!

end Litmus
end PTX
