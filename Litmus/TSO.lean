import Pop.Arch.TSO
namespace Litmus

deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |} 𐄂
  Trace Hint := [Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Accept (R y) at Thread 2, Accept (R x) at Thread 2, Accept (W y = 1) at Thread 3, Accept (R y) at Thread 1, Propagate Request 5 to Thread 1, Propagate Request 5 to Thread 3, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 0, Propagate Request 2 to Thread 2, Propagate Request 2 to Thread 3, Propagate Request 2 to Thread 1, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3, Satisfy Request 7 with Request 1, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 2, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Propagate Request 4 to Thread 3, Satisfy Request 4 with Request 6]
deflitmus IRIW_fences := {| W x=1 ||  R x // 1; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |} 𐄂
  Trace Hint := [Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Accept (R y) at Thread 2, Accept (R x) at Thread 2, Accept (W y = 1) at Thread 3, Accept (R y) at Thread 1, Propagate Request 5 to Thread 1, Propagate Request 5 to Thread 3, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 0, Propagate Request 2 to Thread 2, Propagate Request 2 to Thread 3, Propagate Request 2 to Thread 1, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3, Satisfy Request 7 with Request 1, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 2, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Propagate Request 4 to Thread 3, Satisfy Request 4 with Request 6]
deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
  Trace Hint := [Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 5]
deflitmus MP_fence1 := {| W x=1; Fence; W y=1 ||  R y // 1; R x // 0 |}
  Trace Hint := [Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Propagate Request 6 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 6]
deflitmus MP_fence2 := {| W x=1; W y=1 ||  R y //1; Fence; R x // 0 |}
  Trace Hint := [Accept (R y) at Thread 1, Accept (Fence) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 6 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 6, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1]
deflitmus MP_fence := {| W x=1; Fence; W y=1 ||  R y // 1; Fence; R x // 0|}
deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |}
  Trace Hint := [Accept (W y = 1) at Thread 1, Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 0, Accept (R y) at Thread 0, Satisfy Request 3 with Request 2, Satisfy Request 6 with Request 5, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1, Propagate Request 7 to Thread 1, Satisfy Request 7 with Request 1, Propagate Request 2 to Thread 0]
deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |} ✓
  Trace Hint := [Accept (W y = 1) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R y) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Satisfy Request 5 with Request 1, Propagate Request 2 to Thread 0]
deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |} 𐄂
--deflitmus causality := {| W x = 1 || R x; Fence; W x = 2 || R x; W|}

def allTSO := litmusTests!
def tso_2 := allTSO.filter λ lit => lit.numThreads == 2
def tso_3 := allTSO.filter λ lit => lit.numThreads == 3
def tso_4 := allTSO.filter λ lit => lit.numThreads == 4

end Litmus
