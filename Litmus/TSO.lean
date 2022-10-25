import Pop.Arch.TSO
import Litmus.TSOTraces
namespace Litmus

deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |} 𐄂

deflitmus IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |} 𐄂

deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |} 𐄂

deflitmus MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |} 𐄂

deflitmus MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |} 𐄂

deflitmus MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|} 𐄂

deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |} ✓

deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |} ✓

deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |} 𐄂

deflitmus WWRWRR_fences' := {| W x=1; Fence; W y=1 || R y // 1; Fence; W z = 1 || R z // 1 ; Fence; R x // 0|} 𐄂

def allTSO := litmusTests!
def tso_2 := allTSO.filter λ lit => lit.numThreads == 2
def tso_3 := allTSO.filter λ lit => lit.numThreads == 3
def tso_4 := allTSO.filter λ lit => lit.numThreads == 4

end Litmus
