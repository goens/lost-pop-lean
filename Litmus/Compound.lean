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
  where sys := { {T0, T3}. tso, {T1}. ptx {T2}. ptx}

deflitmus IRIW_tso_one_read_ptx_writes := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
  where sys := { {T0}. ptx {T1}. ptx {T3}. ptx, {T2}. tso}

deflitmus IRIW_tso_fences := {| W x=1 ||  R x // 1 ; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. tso}

deflitmus IRIW_ptx_fences := {| W x=1 ||  R x // 1 ; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T1, T2, T3}. ptx}

deflitmus IRIW_ptx_reads_tso_writes_fences := {| W x=1 ||  R x // 1 ; Fence;  R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |}
  where sys := { {T0, T3}. tso, {T1}. ptx, {T2}. tso}

def allCompound : List Litmus.Test := litmusTests!
def compound_2 := allCompound.filter λ lit => lit.numThreads == 2
def compound_3 := allCompound.filter λ lit => lit.numThreads == 3
def compound_4 := allCompound.filter λ lit => lit.numThreads == 4

end Litmus
