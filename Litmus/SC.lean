-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.Arch.SC
namespace SC
namespace Litmus

deflitmus IRIW := {| W x=1 ||  R x // 1 ; R y // 0 || R y // 1; R x // 0 || W y=1 |} 𐄂

deflitmus MP := {|  W x=1; W y=1 ||  R y // 1; R x // 0 |} 𐄂

deflitmus N7 := {| W x=1; R x // 1; R y //0 || W y=1 || R y // 1; R x //0 |} 𐄂

deflitmus dekkers := {| W x=1; R y //0 || W y=1; R x // 0 |} 𐄂

deflitmus WRC := {| W x=1 || R x // 1; W y = 1 || R y // 1 ;dep R x // 0|} 𐄂

deflitmus MP3 := {| W x=1;  W y=1 || R y // 1; W z = 1 || R z // 1 ; R x // 0|} 𐄂

deflitmus simpleRF := {| W. cta_rlx x=1 || R. cta_rlx x // 1 |} ✓

deflitmus two_plus_two2 := {| W x=1; W y=2;  R y // 1 || W y=1; W x=2 ;  R x // 1|} 𐄂

deflitmus co_two_thread := {| W x = 1; R x // 2 || W x = 2; R x // 1 |} 𐄂

deflitmus lb := {| R x // 1; W y = 1 || R y // 1; W x=1 |} 𐄂

deflitmus r := {| W x = 1; W y = 1 || W y = 2; R x // 0; R y // 2 |} ✓

deflitmus s := {| W x = 2; W y = 1 || R y // 1; W x = 1; R x // 2 |} 𐄂

def allTests := litmusTests!
def tests_2 := allTests.filter λ lit => lit.numThreads == 2
def tests_3 := allTests.filter λ lit => lit.numThreads == 3
def tests_4 := allTests.filter λ lit => lit.numThreads == 4

end Litmus
end SC
