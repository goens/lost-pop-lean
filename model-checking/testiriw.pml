/* Litmus test (IRIW)
 ---------------------

r0:Wx                     r5: Wy
        r1:Rx    r3:Ry
       --sc--    --sc--
        r2:Ry    r4:Rx

*/

/* State: */

/* propagated to threads? */
/* index = request, bits 0..3: propagated to thread $bit */
byte propagated[6];

/* index = req, bit = req' */
byte order_constraints[6];

proctype propagate(byte req; byte thread){
  printf("running propagate %d, %d\n", req, thread);
  if
    :: req > 5 || thread > 4 -> skip;
    :: (propagated[req] >> thread) ^ 1 == 1 -> skip // already propagated
    :: else -> atomic {
      propagated[req] = propagated[req] ^ (1<<thread);
      do
        // req != req', req'.thread == thread,          (req', req) \notin oc         (req, req') \notin oc                req.address == req'.address
        :: (req != 0 && thread == 0 && ((order_constraints[0] >> req) ^ 1 != 1) && ((order_constraints[req] >> 0) ^ 1 != 1) && (req == 1 || req == 4)) -> order_constraints[req] = order_constraints[req] ^ 1  // 000001b
        :: (req != 1 && thread == 1 && ((order_constraints[1] >> req) ^ 1 != 1) && ((order_constraints[req] >> 1) ^ 1 != 1) && (req == 0 || req == 4)) -> order_constraints[req] = order_constraints[req] ^ 2  // 000010b
        :: (req != 2 && thread == 1 && ((order_constraints[2] >> req) ^ 1 != 1) && ((order_constraints[req] >> 2) ^ 1 != 1) && (req == 3 || req == 5)) -> order_constraints[req] = order_constraints[req] ^ 4  // 000100b
        :: (req != 3 && thread == 2 && ((order_constraints[3] >> req) ^ 1 != 1) && ((order_constraints[req] >> 3) ^ 1 != 1) && (req == 2 || req == 5)) -> order_constraints[req] = order_constraints[req] ^ 8  // 001000b
        :: (req != 4 && thread == 2 && ((order_constraints[4] >> req) ^ 1 != 1) && ((order_constraints[req] >> 4) ^ 1 != 1) && (req == 0 || req == 1)) -> order_constraints[req] = order_constraints[req] ^ 16 // 010000b
        :: (req != 5 && thread == 3 && ((order_constraints[5] >> req) ^ 1 != 1) && ((order_constraints[req] >> 5) ^ 1 != 1) && (req == 2 || req == 3)) -> order_constraints[req] = order_constraints[req] ^ 32 // 100000b
        :: else -> break
      od
    }
  fi
  printf("...propagate %d, %d done!", req, thread);
}

proctype thread_0(){
  do
    :: propagated[0] == 15 /* 1111b */ -> break;
    :: if
         :: (propagated[0] >> 1) ^ 1 == 0 -> run propagate(0,1)
         :: (propagated[0] >> 2) ^ 1 == 0 -> run propagate(0,2)
         :: (propagated[0] >> 3) ^ 1 == 0 -> run propagate(0,3)
       fi
  od
}

proctype thread_1(){
    do
         :: propagated[1] == 15 /* 1111b */ -> break;
         :: propagated[1] == propagated[0] && ((order_constraints[0] >> 1) ^ 1 == 1) -> break; // remove read
         :: else ->
             if
                :: (propagated[1] >> 0) ^ 1 == 0 -> run propagate(1,0)
                :: (propagated[1] >> 2) ^ 1 == 0 -> run propagate(1,2)
                :: (propagated[1] >> 3) ^ 1 == 0 -> run propagate(1,3)
             fi
    od
    do
         :: propagated[2] == 15 /* 1111b */ -> break;
         :: propagated[2] == propagated[5] && ((order_constraints[5] >> 2) ^ 1 == 1) -> break; // remove read
         :: else ->
             if
                :: (propagated[2] >> 0) ^ 1 == 0 -> run propagate(2,0)
                :: (propagated[2] >> 2) ^ 1 == 0 -> run propagate(2,2)
                :: (propagated[2] >> 3) ^ 1 == 0 -> run propagate(2,3)
             fi
    od

}
proctype thread_2(){
    do
         :: propagated[3] == 15 /* 1111b */ -> break;
         :: propagated[3] == propagated[5] && ((order_constraints[5] >> 3) ^ 1 == 1) -> break; // remove read
         :: else ->
             if
                :: (propagated[3] >> 0) ^ 1 == 0 -> run propagate(3,0)
                :: (propagated[3] >> 1) ^ 1 == 0 -> run propagate(3,1)
                :: (propagated[3] >> 3) ^ 1 == 0 -> run propagate(3,3)
             fi
    od
    do
         :: propagated[4] == 15 /* 1111b */  -> break;
         :: propagated[4] == propagated[0] && ((order_constraints[0] >> 4) ^ 1 == 1) -> break; // remove read
         :: else ->
             if
                :: (propagated[4] >> 0) ^ 1 == 0 -> run propagate(4,0)
                :: (propagated[4] >> 1) ^ 1 == 0 -> run propagate(4,1)
                :: (propagated[4] >> 3) ^ 1 == 0 -> run propagate(4,3)
             fi
    od

}

proctype thread_3(){
  do
    :: propagated[5] == 15 /* 1111b */ -> break;
    :: if
         :: (propagated[5] >> 0) ^ 1 == 0 -> run propagate(5,0)
         :: (propagated[5] >> 1) ^ 1 == 0 -> run propagate(5,1)
         :: (propagated[5] >> 2) ^ 1 == 0 -> run propagate(5,2)
       fi
  od
}

never
{
  //      { (4,0), (0,1), (2,5), (5,3) \in oc
  ((order_constraints[4] >> 0) ^ 1 == 1) && ((order_constraints[0] >> 1) ^ 1 == 1) &&
  ((order_constraints[2] >> 5) ^ 1 == 1) && ((order_constraints[5] >> 3) ^ 1 == 1)
}

init{
  propagated[0] = 1  // 0001b;
  propagated[1] = 2  // 0010b;
  propagated[2] = 2  // 0010b;
  propagated[3] = 4  // 0100b;
  propagated[4] = 4  // 0100b;
  propagated[5] = 8  // 1000b;

  order_constraints[0] = 0  // 000000b;
  order_constraints[1] = 4  // 000100b;
  order_constraints[2] = 0  // 000000b;
  order_constraints[3] = 16 // 010000b;
  order_constraints[4] = 0  // 000000b;
  order_constraints[5] = 0  // 000000b;

  run thread_0();
  run thread_1();
  run thread_2();
  run thread_3()
}
