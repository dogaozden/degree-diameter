#!/bin/bash
# longer fake-chart runs (90 s CPU, seed 2) on the best pairs: lower bound check for the 15 s screen
D=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r1/c2
cd $C
export THREADS=1
run() { timeout 300 nice -n 10 $D/mlift_chart $D/bases4/$1.txt $2.txt $D/charts/fake_univ.txt 90 2 > logs/long_$1_$2.log 2>&1; echo "$1 $2 $(tail -1 logs/long_$1_$2.log | cut -c1-60)" >> screen/long_summary.txt; }
run k4_012 g17_cyc17
run k4_012 g18_c3xd3
run k4_023 g18_c3xc6
echo DONE >> screen/long_summary.txt
