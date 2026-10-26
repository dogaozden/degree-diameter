#!/bin/bash
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/d1
for spec in "7 3 2 17" "31 6 25 2" "7 6 2 9" "13 3 3 9"; do
  set -- $spec; p=$1; k=$2; r=$3; n=$4
  for s in 3 4 5 6 7 8 9 10 11 12; do
    line=$(THREADS=1 OMP_NUM_THREADS=1 timeout 40 nice -n 10 ../../tools/haar_fast 6 5 10 $s 16 sol_${p}_${k}_${r}_${n}_s${s}.bin meta $p $k $r $n 2>&1 | grep '^RESULT')
    echo "FOLLOW meta $p $k $r $n seed=$s $line" >> follow.log
  done
done
