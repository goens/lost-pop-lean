import Pop.Arch.ARM
namespace ARM
namespace Litmus

hint for WRC := [Accept (R y) at Thread 2, Accept (Fence. rel) at Thread 2, Accept (R x) at Thread 2, Accept (R. acq x) at Thread 1, Accept (W y = 1) at Thread 1, Accept (W x = 1) at Thread 0, Propagate Request 2 to Thread 0, Propagate Request 4 to Thread 0, Propagate Request 4 to Thread 1, Satisfy Request 4 with Request 0, Propagate Request 5 to Thread 2, Propagate Request 7 to Thread 1, Propagate Request 7 to Thread 2, Propagate Request 5 to Thread 0, Satisfy Request 5 with Request 7, Propagate Request 6 to Thread 0, Propagate Request 6 to Thread 2, Propagate Request 2 to Thread 1, Satisfy Request 2 with Request 6]

end Litmus
end ARM

