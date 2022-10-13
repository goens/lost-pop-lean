import Pop.Arch.ARM
namespace Litmus

deflitmus WRC := {| W x=1 || R. acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|}
deflitmus WRC_two_deps := {| W x=1 || R. acq x // 1;dep W y = 1 || R y // 1 ;dep R x // 0|}
deflitmus WRC_rel := {| W. rel x=1 || R. acq x // 1; W y = 1 || R y // 1 ;dep R x // 0|}
deflitmus WRC_acq := {| W x=1 || R. acq x // 1; W y = 1 || R. acq y // 1 ;dep R x // 0|}
deflitmus WRC_no_dep := {| W x=1 || R. acq x // 1; W y = 1 || R y // 1 ; R x // 0|}
deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |}
deflitmus IRIW_3_threads := {| W x=1; W y=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 |}
deflitmus IRIW_acq := {| W x=1 ||  R. acq x // 1;  R. acq y // 0 || R. acq  y // 1; R. acq x // 0 || W y=1 |}
deflitmus IRIW_first_acq := {| W x=1 ||  R. acq x // 1;  R y // 0 || R. acq  y // 1; R x // 0 || W y=1 |}
deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |}
deflitmus MP_rel := {| W. rel x=1; W. rel y=1 ||  R y // 1; R x // 0 |}
deflitmus MP_acq := {| W x=1; W y=1 ||  R. acq y //1; R. acq x // 0 |}
deflitmus MP_relacq := {| W. rel x=1; W. rel y=1 ||  R. acq y //1; R. acq x // 0 |}
deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0 |}
deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |}
deflitmus dekkers_fence := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |}
--def causality := {| W x = 1 || R x; Fence; W x = 2 || R x; W|}

def allARM := litmusTests!
def arm_2 := allARM.filter λ lit => lit.numThreads == 2
def arm_3 := allARM.filter λ lit => lit.numThreads == 3
def arm_4 := allARM.filter λ lit => lit.numThreads == 4

end Litmus
