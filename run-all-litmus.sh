#!/bin/bash

# The number of iterations for the exploration runs.
# The default of 100000 is sufficient for most litmus
# tests with 3 threads or less, litmus tests with 4
# threads are probably not going to be exhaustively
# explored with any reasonable time. With the trace
# hints, a significantly smaller number of iterations
# is sufficient for finding most witnesses, even if
# the exploration is not exhaustive.
NUM_ITERATIONS=10000 #0
ARCHITECTURES=TSO,PTX,Compound,XC,XCTSO

# Build binary in case it's not already built
lake update && lake build

echo "=============================================="
echo "          Running Operational Model"
echo "=============================================="

for ARCH in `echo $ARCHITECTURES | sed 's/,/ /g'`; do
    ./build/bin/pop -e -a $ARCH -i $NUM_ITERATIONS
done


echo "=============================================="
echo "          Running Alloy Axiomatic"
echo "=============================================="
