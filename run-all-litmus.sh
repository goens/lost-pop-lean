#!/bin/bash

# The number of iterations for the exploration runs.
# The commented-out value of 100000 is sufficient for most
# litmus tests with 3 threads or less, litmus tests with 4
# threads are probably not going to be exhaustively
# explored with any reasonable time. With the trace
# hints, a significantly smaller number of iterations
# is sufficient for finding most witnesses, even if
# the exploration is not exhaustive.
NUM_ITERATIONS=10000 #100000
ARCHITECTURES=TSO,PTX,Compound,XC,XCTSO


PROJECT_ROOT=`pwd`
AXIOMATIC_DIR=$PROJECT_ROOT/cmm-axiomatic
ALLOY_JAR=$PROJECT_ROOT/org.alloytools.alloy/org.alloytools.alloy.cli/target/org.alloytools.alloy.cli.jar
OUTPUT=results.csv

echo "=============================================="
echo "          Building Tools"
echo "=============================================="

# Build binary in case it's not already built
lake update && lake build
# Build Alloy
cd org.alloytools.alloy
./gradlew build
cd $PROJECT_ROOT

#cleanup
rm -rf litmus_alloy*

echo "=============================================="
echo "          Running Litmus Tests"
echo "=============================================="


echo "architecture,test,operational,axiomatic" > $OUTPUT
for ARCH in `echo $ARCHITECTURES | sed 's/,/ /g'`; do
   #Build Axiomatic Alloy litmus tests
  # We only have axiomatic for TSO,PTX,Compound
  DIR=litmus_alloy_$ARCH
  ./build/bin/pop -a $ARCH -A -D $DIR
  TESTS=`ls $DIR/*.als`
  cp $AXIOMATIC_DIR/*.als $DIR
  for TESTFILE in $TESTS; do
    TEST=`basename $TESTFILE .als`
     echo -n "Running Litmus Test $ARCH/${TEST}: "
     echo -n $ARCH, >> $OUTPUT
     echo -n $TEST, >> $OUTPUT
    ./build/bin/pop -e -a $ARCH -i $NUM_ITERATIONS -l $TEST | grep -o -e "𐄂" -e "✓" -e "𐄂?" -e " ?" | tr '\n' ',' | cut -d ',' -f 2 | tr '\n' ',' | tee -a $OUTPUT
     #echo -n "," >> $OUTPUT
    if [ "$ARCH" = "TSO" ] || [ "$ARCH" = "PTX" ] || [ "$ARCH" = "Compound" ]; then
      java -jar $ALLOY_JAR exec $TESTFILE 2>> litmus_alloy.log | grep -o -e "INSTANCE" -e "UNSAT" | sed -e 's/INSTANCE/✓/g' -e 's/UNSAT/𐄂/g' | tee -a $OUTPUT
    else
      echo "?" >> $OUTPUT
      echo ""
    fi
  done;
done
cat $OUTPUT
