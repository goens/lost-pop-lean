-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.Arch.CompoundXCTSO

namespace Litmus

hint for IRIW1_sys := [Accept (R y) at Thread 2, Accept (R x) at Thread 2, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 0, Accept (R x) at Thread 1, Accept (R y) at Thread 1, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 5 to Thread 3, Satisfy Request 5 with Request 1, Accept (W y = 1) at Thread 3, Accept (W x = 1) at Thread 0, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 2 to Thread 3, Satisfy Request 2 with Request 6, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3, Satisfy Request 4 with Request 7]

hint for IRIW2_sys := [Accept (R y) at Thread 2, Accept (R x) at Thread 2, Propagate Request 3 to Thread 0, Propagate Request 3 to Thread 1, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 0, Accept (R x) at Thread 1, Accept (R y) at Thread 1, Propagate Request 5 to Thread 0, Propagate Request 5 to Thread 2, Propagate Request 5 to Thread 3, Satisfy Request 5 with Request 1, Accept (W y = 1) at Thread 3, Accept (W x = 1) at Thread 0, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 1, Propagate Request 6 to Thread 2, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 2, Propagate Request 7 to Thread 3, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1, Propagate Request 2 to Thread 3, Satisfy Request 2 with Request 6, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3, Satisfy Request 4 with Request 7]

hint for  IRIW2_sys_F := [Accept (W y = 1) at Thread 3, Accept (R y) at Thread 2, Accept (W x = 1) at Thread 0, Accept (R x) at Thread 1, Propagate Request 4 to Thread 1, Propagate Request 2 to Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 4, Propagate Request 3 to Thread 3, Satisfy Request 3 with Request 2, Accept (Fence. sys_sc) at Thread 2, Accept (R x) at Thread 2, Propagate Request 7 to Thread 0, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 3, Accept (Fence. sys_sc) at Thread 1, Accept (R y) at Thread 1, Satisfy Request 7 with Request 0, Propagate Request 4 to Thread 2, Propagate Request 4 to Thread 3, Propagate Request 9 to Thread 0, Propagate Request 9 to Thread 2, Propagate Request 9 to Thread 3, Satisfy Request 9 with Request 1, Propagate Request 2 to Thread 0, Propagate Request 2 to Thread 1]


end Litmus
