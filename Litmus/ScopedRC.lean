-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.Arch.ScopedRC
namespace ScopedRC
namespace Litmus

deflitmus IRIW := W x=1 || R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1  expect ✓

deflitmus IRIW_relacq := W.sys_rel x=1 || R.sys_acq x // 1 ; R.sys_acq y // 0 || R.sys_acq y // 1; R.sys_acq x // 0 || W.sys_rel y=1

deflitmus IRIW_3ctas := W x=1 || R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1
 where sys := { {T0}, {T1, T2}, {T3} }

deflitmus MP :=  W x=1; W y=1 || R y // 1; R x // 0

deflitmus MP_rel_acq := W x=1; W.sys_rel y=1 || R.sys_acq y // 1; R x // 0

deflitmus N7 := W x=1; R x // 1; R y //0 || W y=1; R y // 1; R x //0

deflitmus dekkers := W x=1; R y //0 || W y=1; R x // 0

deflitmus dekkers_acqrel := W.sys_rel x=1; R.sys_acq y //0 || W.sys_rel y=1; R.sys_acq x // 0

deflitmus WRC := W x=1 || R.sys_acq x // 1; W y = 1 || R y // 1 ; R x // 0

deflitmus WRC_acqrel := W x=1 || R.sys_acq x // 1; W.sys_rel y = 1 || R.sys_acq y // 1 ; R.sys_acq x // 0

deflitmus ISA2 := W x=1; W y=1 || R y // 1; W z = 1 || R z // 1 ; R x // 0

deflitmus ISA2_acqrel := W.cta_rel x=1; W.cta_rel y=1 || R.cta_acq y // 1; W.cta_rel z = 1 || R.cta_acq z // 1 ; R.cta_acq x // 0

def allTests : List Litmus.Test := litmusTests!
def tests_2 := allTests.filter λ lit => lit.numThreads == 2
def tests_3 := allTests.filter λ lit => lit.numThreads == 3
def tests_4 := allTests.filter λ lit => lit.numThreads == 4

end Litmus
end ScopedRC
