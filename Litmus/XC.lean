-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

-- There's no axiomatic model for XC, here the axiomatic annotations refer to the simulator results.

import Pop.Arch.XC
import Litmus.XCTraces
namespace XC
namespace Litmus

deflitmus MP_sys := {| W x=1; W y=1 ||  R y // 1; R x // 0|} ✓

deflitmus MP_sys_F := {| W x=1; Fence; W y=1 ||  R y //1; Fence; R x // 0 |} 𐄂

deflitmus MP_cta_F := {| W x=1; Fence. cta_sc; W y=1 ||  R y // 1; Fence. cta_sc; R x // 0|}
  where sys := { {T0}, {T1} } ✓

deflitmus SB_sys := {| W x=1; R y //0 || W y=1; R x // 0 |}  ✓

deflitmus SB_sys_F := {| W x=1; Fence; R y //0 || W y=1; Fence;  R x // 0 |} 𐄂

deflitmus IRIW_sys := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |} ✓

deflitmus IRIW_sys_F := {| W x=1 ||  R x // 1 ; Fence; R y // 0 || R y // 1; Fence; R x // 0 || W y=1 |} 𐄂

deflitmus LB_sys := {| R x // 1; W y = 1 || R y // 1; W x=1 |} 𐄂

def allTests : List Litmus.Test := litmusTests!
def tests_2 := allTests.filter λ lit => lit.numThreads == 2
def tests_3 := allTests.filter λ lit => lit.numThreads == 3
def tests_4 := allTests.filter λ lit => lit.numThreads == 4

end Litmus
end XC
