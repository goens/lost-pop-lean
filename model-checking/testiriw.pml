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
byte propagated[6] = 0;

/* index = req, bit = req' */
byte order_constraints[6] = 0;

proctype thread_0(){
  do
    :: propagated[0] == 15 /* 1111b */ -> break;
    :: if
         :: ((propagated[0] >> 1) & 1) == 0 -> atomic { printf("propagating req 0 to thread 1\n"); propagated[0] = propagated[0] ^ (1 << 1);
                                                      if
                                                        :: printf("adding oc (0, 1)\n"); (((order_constraints[1] >> 0) & 1) == 0) -> order_constraints[0] = order_constraints[0] ^ 2 /* 000010b */
                                                        :: else -> skip
                                                      fi
                                                     }
         :: ((propagated[0] >> 2) & 1) == 0 -> atomic { printf("propagating req 0 to thread 2\n"); propagated[0] = propagated[0] ^ (1 << 2);
                                                      if
                                                        :: printf("adding oc (0, 4)\n"); (((order_constraints[4] >> 0) & 1) == 0) -> order_constraints[0] = order_constraints[0] ^ 16 /* 010000b */
                                                        :: else -> skip
                                                      fi
                                                     }
         :: ((propagated[0] >> 3) & 1) == 0 -> atomic { printf("propagating req 0 to thread 3\n"); propagated[0] = propagated[0] ^ (1 << 3) }
       fi
  od
}

proctype thread_1(){
    do
         :: propagated[1] == 15 /* 1111b */ -> break;
         :: propagated[1] == propagated[0] & (((order_constraints[0] >> 1) & 1) == 1) -> break; // remove read
         :: else ->
             if
                :: ((propagated[1] >> 0) & 1) == 0 -> atomic { printf("propagating req 1 to thread 0\n"); propagated[1] = propagated[1] ^ (1 << 0);
                                                      if
                                                        :: (((order_constraints[0] >> 1) & 1) == 0) -> printf("adding oc (1, 0)\n"); order_constraints[1] = order_constraints[1] ^ 1 /* 000001b */
                                                        :: else -> skip
                                                      fi
                }
                :: ((propagated[1] >> 2) & 1) == 0 -> atomic { printf("propagating req 1 to thread 2\n"); propagated[1] = propagated[1] ^ (1 << 2) }
                :: ((propagated[1] >> 3) & 1) == 0 -> atomic { printf("propagating req 1 to thread 3\n"); propagated[1] = propagated[1] ^ (1 << 3) }
             fi
    od
    do // predecessors
      :: (((order_constraints[0] >> 1) & 1) == 1) -> propagated[0] == 15; break
      :: else -> break
    od
    do
         :: propagated[2] == 15 /* 1111b */ -> break;
         :: propagated[2] == propagated[5] & (((order_constraints[5] >> 2) & 1) == 1) -> break; // remove read
         :: else ->
             if
                :: ((propagated[2] >> 0) & 1) == 0 -> atomic { printf("propagating req 2 to thread 0\n"); propagated[2] = propagated[2] ^ (1 << 0)}
                :: ((propagated[2] >> 2) & 1) == 0 -> atomic { printf("propagating req 2 to thread 2\n"); propagated[2] = propagated[2] ^ (1 << 2) }
                :: ((propagated[2] >> 3) & 1) == 0 -> atomic { printf("propagating req 2 to thread 3\n"); propagated[2] = propagated[2] ^ (1 << 3);
                                                      if
                                                        :: (((order_constraints[5] >> 2) & 1) == 0) -> printf("adding oc (2, 5)\n"); order_constraints[2] = order_constraints[2] ^ 32 /* 100000b */
                                                        :: else -> skip
                                                      fi
                }
             fi
    od
}

proctype thread_2(){
    do
         :: propagated[3] == 15 /* 1111b */ -> break;
         :: propagated[3] == propagated[5] & (((order_constraints[5] >> 3) & 1) == 1) -> break; // remove read
         :: else ->
             if
                :: ((propagated[3] >> 0) & 1) == 0 -> atomic { printf("propagating req 3 to thread 0\n"); propagated[3] = propagated[3] ^ (1 << 0) }
                :: ((propagated[3] >> 1) & 1) == 0 -> atomic { printf("propagating req 3 to thread 1\n"); propagated[3] = propagated[3] ^ (1 << 1) }
                :: ((propagated[3] >> 3) & 1) == 0 -> atomic { printf("propagating req 3 to thread 3\n"); propagated[3] = propagated[3] ^ (1 << 3);
                                                      if
                                                        :: (((order_constraints[5] >> 3) & 1) == 0) -> printf("adding oc (3, 5)\n"); order_constraints[3] = order_constraints[3] ^ 32 /* 100000b */
                                                        :: else -> skip
                                                      fi
               }
             fi
    od
    do // predecessors
      :: (((order_constraints[5] >> 3) & 1) == 1) -> propagated[5] == 15; break
      :: else -> break
    od
    do
         :: propagated[4] == 15 /* 1111b */  -> break;
         :: propagated[4] == propagated[0] & (((order_constraints[0] >> 4) & 1) == 1) -> break; // remove read
         :: else ->
             if
                :: ((propagated[4] >> 0) & 1) == 0 -> atomic { printf("propagating req 4 to thread 0\n"); propagated[4] = propagated[4] ^ (1 << 0);
                                                      if
                                                        :: (((order_constraints[0] >> 4) & 1) == 0) -> printf("adding oc (4, 0)\n"); order_constraints[4] = order_constraints[4] ^ 1 /* 000001b */
                                                        :: else -> skip
                                                      fi
               }
                :: ((propagated[4] >> 1) & 1) == 0 -> atomic { printf("propagating req 4 to thread 1\n"); propagated[4] = propagated[4] ^ (1 << 1) }
                :: ((propagated[4] >> 3) & 1) == 0 -> atomic { printf("propagating req 4 to thread 3\n"); propagated[4] = propagated[4] ^ (1 << 3) }
             fi
    od

}

proctype thread_3(){
  do
    :: propagated[5] == 15 /* 1111b */ -> break;
    :: if
         :: ((propagated[5] >> 0) & 1) == 0 -> atomic { printf("propagating req 5 to thread 0\n"); propagated[5] = propagated[5] ^ (1 << 0) }
         :: ((propagated[5] >> 1) & 1) == 0 -> atomic { printf("propagating req 5 to thread 1\n"); propagated[5] = propagated[5] ^ (1 << 1);
                                                      if
                                                        :: (((order_constraints[2] >> 5) & 1) == 0) -> printf("adding oc (5, 2)\n"); order_constraints[5] = order_constraints[5] ^ 4 /* 000100b */
                                                        :: else -> skip
                                                      fi
         }
         :: ((propagated[5] >> 2) & 1) == 0 -> atomic { printf("propagating req 5 to thread 2\n"); propagated[5] = propagated[5] ^ (1 << 2);
                                                     if
                                                        :: (((order_constraints[3] >> 5) & 1) == 0) -> printf("adding oc (5, 3)\n"); order_constraints[5] = order_constraints[5] ^ 8 /* 001000b */
                                                        :: else -> skip
                                                      fi
         }
       fi
  od
}

never
{
  do
    /* invalid condition threads read (1,0) (1,0) */
     ::  assert( !(
         //      { (4,0), (0,1), (2,5), (5,3) \in oc
         (((order_constraints[4] >> 0) & 1) == 1) && ((order_constraints[0] >> 1) & 1 == 1) &&
            (((order_constraints[2] >> 5) & 1) == 1) && ((order_constraints[5] >> 3) & 1 == 1)
         ))
    /* valid condition: both read 1s
     ::  assert( !(
         //      { (0,4), (0,1), (5,2), (5,3) \in oc
         (((order_constraints[0] >> 4) & 1) == 1) && ((order_constraints[0] >> 1) & 1 == 1) &&
            (((order_constraints[5] >> 2) & 1) == 1) && ((order_constraints[5] >> 3) & 1 == 1)
         ))
     */
  od
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
