#!/bin/bash

# Parameters
MAX_ITERATIONS=1000
ARCHS="TSO PTX Compound"
# First make sure project is up to date and compiled.
lake update && lake build

#Run LOST-POP
for ARCH in $ARCHS; do
  ./build/bin/pop -a $ARCH -e -i $MAX_ITERATIONS
  ./build/bin/pop -a $ARCH -A
done
