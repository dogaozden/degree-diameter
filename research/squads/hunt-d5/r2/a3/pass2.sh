#!/bin/bash
# pass 2: best five distinct groups of pass 1, 60 s each (seed 3); then the parallel-edge base 2I+P1+P2+P3, 6 s, top five groups
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/a3
export OMP_NUM_THREADS=1 THREADS=1
for gi in 39_2 40_11 40_9 40_2 40_3; do
  N=${gi%_*}; I=${gi#*_}
  out=$(timeout 90 nice -n 10 ../../tools/flift K55.txt g${N}_${I}.bin 5 5 60 3 8 sol/p2_${N}_${I}_s3 2>&1 | grep RESULT)
  echo "PASS2 K55 $N $I seed=3 60s $out"
done > pass2.log 2>&1
for gi in 39_2 40_11 40_9 40_2 40_3; do
  N=${gi%_*}; I=${gi#*_}
  out=$(timeout 40 nice -n 10 ../../tools/flift K55_2I_P1P2P3.txt g${N}_${I}.bin 5 5 6 1 8 sol/v_${N}_${I}_s1 2>&1 | grep RESULT)
  echo "VARIANT 2I+P1+P2+P3 $N $I seed=1 6s $out"
done >> pass2.log 2>&1
echo PASS2DONE >> pass2.log
