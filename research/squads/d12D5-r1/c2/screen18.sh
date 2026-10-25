#!/bin/bash
# fake-chart screen over the order-18 groups at m = 72, seed 1, 15 s CPU each. usage: screen18.sh BASENAME...
D=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r1/c2
cd $C
export THREADS=1
for b in "$@"; do
  for g in g18_cyc18 g18_dih9 g18_c3xc6 g18_c3xd3; do
    timeout 120 nice -n 10 $D/mlift_chart $D/bases4/$b.txt $g.txt $D/charts/fake_univ.txt 15 1 > logs/${b}_${g}.log 2>&1
    echo "$b $g $(tail -1 logs/${b}_${g}.log | cut -c1-60)" >> screen/g18_summary.txt
  done
done
echo DONE >> screen/g18_summary.txt
