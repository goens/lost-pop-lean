#!/bin/bash

echo "Running simulation litmus tests..."
cd simulation
./run-all-litmus.sh
echo "Running models litmus tests..."
cd ../models
./run-all-litmus.sh
cd ../

TABLE1='table1.csv'
TABLE2='table2.csv'

echo "============================================================="
echo -e '                    ' "Table-1 Results" 
echo "=============================================================" 
echo -e "Test,x86-Gem5,x86TSO,XC-GEM5,SCOPED XC" > $TABLE1

for i in MP SB IRIW LB
do 
    for j in -sys -sys-F -cta-F
    do
        if [[ $j == "-cta-F" ]]; then
            if [[ $i != "MP" ]]; then
                continue
            fi
        fi
        if [[ $j == "-sys-F" ]]; then
            if [[ $i == "LB" ]]; then
                continue
            fi
        fi
        k=$i
        k+=$j
        simCPUOnly=$(grep "CPU-Only,$k," simulation/results.csv | cut -d ',' -f3) 
        simGPUOnly=$(grep -inr "GPU-Only,$k," simulation/results.csv | cut -d ',' -f3)
        l=$i
        if [[ $i == "LB" ]]; then 
            l="lb"
        fi
        if [[ $i == "SB" ]]; then
            l="dekkers"
        fi
        if [[ $j == "-sys" ]]; then
            l+=","
        else
            l+=$j
        fi 
        m=$i
        if [[ $j == "-sys" ]]; then
            m+="_sys,"
        else
            if [[ $j == "-sys-F" ]]; then
                m+="_sys_F,"
            else
                m+="_cta_F,"
            fi
        fi

        modCPUOnly=$(grep "TSO,$l" models/results.csv | cut -d ',' -f3)
        modGPUOnly=$(grep "XC,$m" models/results.csv | cut -d ',' -f3)
        echo -e "$k,${simCPUOnly,,},${modCPUOnly,,},${simGPUOnly,,},${modGPUOnly,,}" >> $TABLE1
    done
done
csvtool readable $TABLE1
echo "--------------------------------------------------------------"

echo -e '\n'

echo "==============================================================" 
echo -e '                    ' "Table-2 Results"
echo "==============================================================" 
echo -e "Test,SWMR,No-SWMR,Model" > $TABLE2

for i in MP1 MP2 SB IRIW1 IRIW2 LB
do
    for j in -sys -sys-F -cta-F
    do
        if [[ $j == "-cta-F" ]]; then
            if [[ $i != "MP1" ]]; then
                continue
            fi
        fi
        if [[ $j == "-sys-F" ]]; then
            if [[ $i == "LB" || $i == "IRIW1" ]]; then
                continue;
            fi
        fi
        k=$i
        k+=$j
        simSWMR=$(grep "Compound,$k," simulation/results.csv | cut -d ',' -f3) 
        simNoSWMR=$(grep "Compound_no_SWMR,$k," simulation/results.csv | cut -d ',' -f3)
        m=$i
        if [[ $j == "-sys" ]]; then
            m+="_sys,"
        else
            if [[ $j == "-sys-F" ]]; then
                m+="_sys_F,"
            else
                m+="_cta_F,"
            fi
        fi
        modComp=$(grep "XCTSO,$m" models/results.csv | cut -d ',' -f3)
        echo -e "$k,${simSWMR,,},${simNoSWMR,,},${modComp,,}" >> $TABLE2
    done 
done 
csvtool readable $TABLE2
echo "--------------------------------------------------------------"
echo -e '\n'

