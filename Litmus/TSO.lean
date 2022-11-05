import Pop.Arch.TSO
import Litmus.TSOTraces
namespace x86
namespace Litmus

deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |} 𐄂

deflitmus IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |} 𐄂

deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |} 𐄂

deflitmus MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |} 𐄂

deflitmus MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |} 𐄂

deflitmus MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|} 𐄂

deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1 || R y // 1; R x //0 |} ✓

deflitmus N7_fence := {| W x=1; Fence; R x // 1; R y //0 || W y=1 || R y // 1; R x //0 |} 𐄂

deflitmus N7_two_threads := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |} ✓

deflitmus N7_two_threads_fences := {| W x=1; Fence; R x // 1; R y //0 || W y=1; Fence; R y // 1; R x //0 |} 𐄂

deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |} ✓

deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |} 𐄂

deflitmus WWRWRR_fences' := {| W x=1; Fence; W y=1 || R y // 1; Fence; W z = 1 || R z // 1 ; Fence; R x // 0|} 𐄂

deflitmus WRC := {| W x=1 || R x // 1; W y = 1 || R y // 1 ;dep R x // 0|} 𐄂

deflitmus MP3 := {| W x=1;  W y=1 || R y // 1; W z = 1 || R z // 1 ; R x // 0|} 𐄂

def allTests := litmusTests!
def tests_2 := allTests.filter λ lit => lit.numThreads == 2
def tests_3 := allTests.filter λ lit => lit.numThreads == 3
def tests_4 := allTests.filter λ lit => lit.numThreads == 4

end Litmus
end x86
