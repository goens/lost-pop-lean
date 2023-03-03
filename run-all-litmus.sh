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
ARCHITECTURES_ALLOY=TSO,PTX,Compound

PROJECT_ROOT=`pwd`
AXIOMATIC_DIR=$PROJECT_ROOT/cmm-axiomatic
ALLOY_JAR=$PROJECT_ROOT/org.alloytools.alloy/org.alloytools.alloy.cli/target/org.alloytools.alloy.cli.jar
OUTPUT=axiomatic_results.csv
OUTPUT_OPERATIONAL=operational_results.csv

# Build binary in case it's not already built
lake update && lake build

echo "=============================================="
echo "          Running Operational Model"
echo "=============================================="

# Cleanup
rm $OUTPUT_OPERATIONAL
for ARCH in `echo $ARCHITECTURES | sed 's/,/ /g'`; do
    ./build/bin/pop -e -a $ARCH -i $NUM_ITERATIONS | tee -a $OUTPUT_OPERATIONAL
done


echo "=============================================="
echo "          Running Alloy Axiomatic"
echo "=============================================="

# Build Alloy
cd org.alloytools.alloy
./gradlew build
cd $PROJECT_ROOT

#cleanup
rm -rf litmus_alloy*

echo "architecture,test,expected,result" > $OUTPUT
for ARCH in `echo $ARCHITECTURES_ALLOY | sed 's/,/ /g'`; do
   #Build Axiomatic Alloy litmus tests
  DIR=litmus_alloy_$ARCH
  ./build/bin/pop -a $ARCH -A -D $DIR
  TESTS=`ls $DIR/*.als`
  cp $AXIOMATIC_DIR/*.als $DIR
  for TEST in $TESTS; do
     echo -n $ARCH, >> $OUTPUT
     echo -n ${TEST##*/}, >> $OUTPUT
     grep "// Expected:" $TEST | grep -o -e "?" -e "𐄂" -e "✓" | tr -d '\n' >> $OUTPUT
     echo -n "," >> $OUTPUT
     java -jar $ALLOY_JAR exec $TEST | grep -o -e "INSTANCE" -e "UNSAT" | sed -e 's/INSTANCE/✓/g' -e 's/UNSAT/𐄂/g'  >> $OUTPUT 2>> litmus_alloy.log
  done;
done
cat $OUTPUT
