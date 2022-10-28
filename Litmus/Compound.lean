import Pop.Arch.Compound
import Litmus.CompoundTraces
namespace Litmus

deflitmus IRIW_tso := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. x86}

deflitmus IRIW_ptx := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. ptx}

deflitmus IRIW_tso_reads_ptx_writes := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T3}. ptx, {T1, T2}. tso}

deflitmus IRIW_ptx_reads_tso_writes := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0, T3}. tso, {T1}. ptx, {T2}. ptx}

deflitmus IRIW_tso_one_read_ptx_writes := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0}. ptx, {T1}. ptx, {T3}. ptx, {T2}. tso}

deflitmus IRIW_tso_fences := {| W x=1 ||  R x // 1 ; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. tso}

deflitmus IRIW_ptx_fences := {| W x=1 ||  R x // 1 ; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. ptx}

deflitmus IRIW_ptx_reads_tso_writes_fences := {| W x=1 ||  R x // 1 ; Fence;  R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T3}. tso, {T1}. ptx, {T2}. tso}

deflitmus MP_tso := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0, T1}. tso}

deflitmus MP_ptx := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0, T1}. ptx}

deflitmus MP_writes_tso := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. tso, {T1}. ptx}

deflitmus MP_writes_ptx := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. ptx, {T1}. tso}

deflitmus MP_writes_tso_ptx_acq_sys := {|  W x=1; W y=1 ||  R. sys_acq y // 1; R x // 0 |}
  where sys := { {T0}. tso, {T1}. ptx}

deflitmus MP_writes_tso_ptx_acq_cta := {|  W x=1; W y=1 ||  R. cta_acq y // 1; R x // 0 |}
  where sys := { {T0}. tso, {T1}. ptx}

deflitmus MP_writes_tso_ptx_acq_sys_fence := {|  W x=1; W y=1 ||  R y // 1; Fence. sys_acq; R x // 0 |}
  where sys := { {T0}. tso, {T1}. ptx}

deflitmus MP_writes_tso_ptx_acq_cta_fence := {|  W x=1; W y=1 ||  R y // 1; Fence. cta_acq; R x // 0 |}
  where sys := { {T0}. tso, {T1}. ptx}

deflitmus MP_writes_ptx_rel_sys := {|  W x=1; W. sys_rel y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. ptx, {T1}. tso}

deflitmus MP_writes_ptx_rel_cta := {|  W x=1; W. cta_rel y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. ptx, {T1}. tso}

deflitmus MP_writes_ptx_rel_sys_fence := {|  W x=1; Fence. sys_rel; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. ptx, {T1}. tso}

deflitmus MP_writes_ptx_rel_cta_fence := {|  W x=1; Fence. cta_rel; W y=1 ||  R y // 1; R x // 0 |}
  where sys := { {T0}. ptx, {T1}. tso}

def allCompound : List Litmus.Test := litmusTests!
def compound_2 := allCompound.filter λ lit => lit.numThreads == 2
def compound_3 := allCompound.filter λ lit => lit.numThreads == 3
def compound_4 := allCompound.filter λ lit => lit.numThreads == 4

end Litmus
