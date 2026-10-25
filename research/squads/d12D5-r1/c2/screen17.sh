#!/bin/bash
# fake-chart screen: all 26 k=4 bases over Z_17 (m=68), 15 s CPU each, seed 1
D=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r1/c2
cd $C
export THREADS=1
for f in $D/bases4/k4_0*.txt; do
  b=$(basename $f .txt)
  timeout 120 nice -n 10 $D/mlift_chart $f g17_cyc17.txt $D/charts/fake_univ.txt 15 1 > logs/${b}_g17.log 2>&1
  echo "$b $(tail -1 logs/${b}_g17.log | cut -c1-60)" >> screen/g17_summary.txt
done
echo DONE >> screen/g17_summary.txt
