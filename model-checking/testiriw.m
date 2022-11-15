-----------------------------------------------
--           Litmus test (IRIW)              --
-----------------------------------------------
--                                           --
--    r0:Wx                     r5: Wy       --
--            r1:Rx    r3:Ry                 --
--           --sc--    --sc--                --
--            r2:Ry    r4:Rx                 --
--                                           --
-----------------------------------------------

const
  NUM_REQS : 6;
  NUM_THREADS : 4;
type
  req_t : 0..(NUM_REQS -1);
  thread_t : 0..(NUM_THREADS - 1);
  thread_arr_t : array [thread_t] of boolean;
  req_arr_t : array [req_t] Of boolean;
var
  propagated : array [req_t] Of thread_arr_t;
  order_constraints : array [req_t] Of req_arr_t;

procedure propagate(var req : req_t; thread : thread_t);
begin
    if propagated[req][thread] == false  then
      propagated[req][thread] := true;
      switch req
      case 0 :
          switch thread
          case 1 :
              if (order_constraints[0][1] == false && order_constraints[1][0] == false) then
                  order_constraints[0][1] := true;
              endif;
          case 2:
              if (order_constraints[0][4] == false && order_constraints[4][0] == false) then
                  order_constraints[0][4] := true;
              endif;
          endswitch;
      case 1 :
          switch thread
          case 0 :
              if (order_constraints[0][1] == false && order_constraints[1][0] == false) then
                  order_constraints[1][0] := true;
              endif;
          endswitch;
      case 2 :
          switch thread
          case 3 :
              if (order_constraints[2][5] == false && order_constraints[5][2] == false) then
                  order_constraints[2][5] := true;
              endif;
          endswitch;
      case 3 :
          switch thread
          case 3 :
              if (order_constraints[3][5] == false && order_constraints[5][3] == false) then
                  order_constraints[3][5] := true;
              endif;
          endswitch;
      case 4 :
          switch thread
          case 0 :
              if (order_constraints[0][4] == false && order_constraints[4][0] == false) then
                  order_constraints[4][0] := true;
              endif;
          endswitch;
      case 5 :
          switch thread
          case 1 :
              if (order_constraints[5][2] == false && order_constraints[2][5] == false) then
                  order_constraints[5][2] := true;
              endif;
          case 2:
              if (order_constraints[5][3] == false && order_constraints[3][5] == false) then
                  order_constraints[5][3] := true;
              endif;
          endswitch;
      endswitch;
      endif;
endprocedure;

procedure reset();
begin
    for i : req_t do
        for j : thread_t do
            propagated[i][j] := false;
        endfor;
    endfor;
    propagated[0][0] := true;
    propagated[1][1] := true;
    propagated[2][1] := true;
    propagated[3][2] := true;
    propagated[4][2] := true;
    propagated[5][3] := true;
    for i : req_t do
        for j : req_t do
            order_constraints[i][j] := false;
        endfor;
    endfor;
endprocedure;

startstate "Init"
    undefine propagated;
    undefine order_constraints;
    reset();
end;

ruleset i : req_t; j : thread_t do
    rule "propagate_rule"
        propagated[i][j] = false &&
        ((i != 1) ||
          -- satisfy read (don't continue to propagate after)
          !(propagated[2][0] || propagated[2][2] || propagated[2][3]))
        &&
        ((i != 2) ||
            -- satisfy read: same propagation + oc
            (((propagated[0][0] == propagated[1][0] && 
              propagated[0][1] == propagated[1][1] && 
              propagated[0][2] == propagated[1][2] && 
              propagated[0][3] == propagated[1][3] &&
              order_constraints[0][1] == true) 
              &&
              -- predecessors
              (propagated[0][0] && propagated[0][1] && 
               propagated[0][2] && propagated[0][3]))
           ||
             (propagated[1][0] == true && 
              propagated[1][1] == true && 
              propagated[1][2] == true && 
              propagated[1][3] == true &&
              order_constraints[1][0] == true)) -- read from mem
        )
        &&
        ((i != 3) ||
          -- satisfy read (don't continue to propagate after)
          !(propagated[4][0] || propagated[4][1] || propagated[4][3]))
        &&
        ((i != 4) ||
            -- satisfy read: same propagation + oc
            (((propagated[5][0] == propagated[3][0] && 
               propagated[5][1] == propagated[3][1] && 
               propagated[5][2] == propagated[3][2] && 
               propagated[5][3] == propagated[3][3] &&
               order_constraints[5][3] == true)
               &&
               -- predecessors
               (propagated[5][0] && propagated[5][1] && 
                propagated[5][2] && propagated[5][3]))
            || 
            (propagated[3][0] == true && 
             propagated[3][1] == true && 
             propagated[3][2] == true && 
             propagated[3][3] == true &&
             order_constraints[3][5] == true)) -- read from mem
        )
        ==>
        propagate(i,j);
     end;
end;

rule "reset"
  true ==> reset();
end;

invariant "forbidden result: x = 1; y = 0 || y = 1; x = 0"
    --  { (4,0), (0,1), (2,5), (5,3) } \in oc
    !(order_constraints[4][0] && order_constraints[0][1] &&
      order_constraints[2][5] && order_constraints[5][3])


-- invariant "x = 0; y = 0 || y = 0; x = 0"
--     !(order_constraints[4][0] && order_constraints[1][0] &&
--       order_constraints[2][5] && order_constraints[3][5])

-- invariant "x = 1; y = 0 || y = 0; x = 0"
--     !(order_constraints[0][4] && order_constraints[1][0] &&
--       order_constraints[2][5] && order_constraints[3][5])

-- invariant "x = 0; y = 1 || y = 0; x = 0"
--     !(order_constraints[0][4] && order_constraints[1][0] &&
--       order_constraints[2][5] && order_constraints[3][5])

-- invariant "x = 0; y = 0 || y = 1; x = 0"
--     !(order_constraints[4][0] && order_constraints[1][0] &&
--       order_constraints[5][2] && order_constraints[3][5])

-- invariant "x = 0; y = 0 || y = 0; x = 1"
--     !(order_constraints[4][0] && order_constraints[1][0] &&
--       order_constraints[2][5] && order_constraints[5][3])

-- invariant "x = 1; y = 1 || y = 0; x = 0"
--    !(order_constraints[0][4] && order_constraints[0][1] &&
--      order_constraints[2][5] && order_constraints[3][5])

-- invariant "x = 0; y = 0 || y = 1; x = 1"
--     !(order_constraints[4][0] && order_constraints[1][0] &&
--       order_constraints[5][2] && order_constraints[5][3])

-- invariant "x = 0; y = 1 || y = 0; x = 1"
--     !(order_constraints[0][4] && order_constraints[1][0] &&
--       order_constraints[5][2] && order_constraints[3][5])

-- invariant "x = 1; y = 0 || y = 1; x = 1"
--     !(order_constraints[0][4] && order_constraints[0][1] &&
--       order_constraints[2][5] && order_constraints[5][3])

-- invariant "x = 1; y = 1 || y = 0; x = 1"
--     !(order_constraints[0][4] && order_constraints[0][1] &&
--       order_constraints[5][2] && order_constraints[3][5])

-- invariant "x = 1; y = 1 || y = 1; x = 0"
--     !(order_constraints[4][0] && order_constraints[0][1] &&
--       order_constraints[5][2] && order_constraints[5][3])

-- invariant "x = 1; y = 1 || y = 1; x = 1"
--     !(order_constraints[0][4] && order_constraints[0][1] &&
--       order_constraints[5][2] && order_constraints[5][3])