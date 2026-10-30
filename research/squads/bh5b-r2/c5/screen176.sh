#!/bin/bash
cd /home/user/degree-diameter/research/squads/bh5b-r2/c5
for i in 41 35 29 27 34 33 7 6 36 28 42 39; do
  for b in b22_15 b22_33 b22_24; do
    out=$(D=5 SECS=10 SEED=1 OUT=sols/s176_${b}_${i}.txt timeout 100 nice -n 10 ./vl bases/$b.txt grp176/sg_176_$i.txt 2>&1 | grep RESULT)
    echo "176_$i $b $out" >> screen176.log
  done
done
echo DONE >> screen176.log
