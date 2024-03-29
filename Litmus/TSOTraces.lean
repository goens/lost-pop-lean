-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.Arch.TSO
namespace x86
namespace Litmus

hint for IRIW := [Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Accept (R y) at Thread 2, Accept (R x) at Thread 2, Accept (W y = 1) at Thread 3, Accept (R y) at Thread 1, Propagate Request 5 to Thread 1, Propagate Request 5 to Thread 3, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 0, Propagate Request 2 to Thread 2, Propagate Request 2 to Thread 3, Propagate Request 2 to Thread 1, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3, Satisfy Request 7 with Request 1, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 2, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Propagate Request 4 to Thread 3, Satisfy Request 4 with Request 6]

hint for IRIW_fences := [Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Accept (R y) at Thread 2, Accept (R x) at Thread 2, Accept (W y = 1) at Thread 3, Accept (R y) at Thread 1, Propagate Request 5 to Thread 1, Propagate Request 5 to Thread 3, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 0, Propagate Request 2 to Thread 2, Propagate Request 2 to Thread 3, Propagate Request 2 to Thread 1, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 2, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3, Satisfy Request 7 with Request 1, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 2, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Propagate Request 4 to Thread 3, Satisfy Request 4 with Request 6]

hint for MP := [Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 5]

hint for MP_fence1 := [Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (Fence) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Propagate Request 6 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 6]

hint for MP_fence2 := [Accept (R y) at Thread 1, Accept (Fence) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (W y = 1) at Thread 0, Propagate Request 6 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 6, Propagate Request 3 to Thread 0, Propagate Request 4 to Thread 0, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 1]

hint for N7_two_threads := [Accept (W y = 1) at Thread 1, Accept (R y) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 0, Accept (R y) at Thread 0, Satisfy Request 3 with Request 2, Satisfy Request 6 with Request 5, Propagate Request 4 to Thread 0, Propagate Request 7 to Thread 1, Satisfy Request 4 with Request 0, Satisfy Request 7 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 5 to Thread 1]

hint for N7 := [Accept (R y) at Thread 2, Accept (R x) at Thread 2, Accept (W y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 0, Accept (R y) at Thread 0, Satisfy Request 6 with Request 5, Propagate Request 4 to Thread 2, Propagate Request 7 to Thread 1, Propagate Request 4 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 2 to Thread 0, Satisfy Request 2 with Request 4, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Satisfy Request 3 with Request 0, Propagate Request 7 to Thread 2, Satisfy Request 7 with Request 1, Propagate Request 5 to Thread 1, Propagate Request 5 to Thread 2]

hint for dekkers := [Accept (W y = 1) at Thread 1, Accept (R x) at Thread 1, Accept (W x = 1) at Thread 0, Accept (R y) at Thread 0, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 0, Propagate Request 4 to Thread 1, Propagate Request 5 to Thread 1, Satisfy Request 5 with Request 1, Propagate Request 2 to Thread 0]

hint for WRC := [Accept (R y) at Thread 2, Accept (R x) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 5 to Thread 1, Propagate Request 3 to Thread 0, Satisfy Request 3 with Request 5, Propagate Request 4 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 4, Accept (R x) at Thread 2, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Satisfy Request 6 with Request 0, Propagate Request 4 to Thread 0, Propagate Request 5 to Thread 2]

-- hint for two_rmws := [Accept (R x) at Thread 1, Accept (W x n + 1) at Thread 1, Accept (R x) at Thread 1, Accept (R x) at Thread 0, Accept (W x n + 1) at Thread 0, Accept (R x) at Thread 0, Propagate Request 1 to Thread 0, Satisfy Request 1 with Request 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Satisfy Request 3 with Request 2, Satisfy Request 6 with Request 5, Propagate Request 2 to Thread 0, Propagate Request 5 to Thread 1]

end Litmus
end x86
