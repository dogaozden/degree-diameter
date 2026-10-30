#!/bin/bash
cd /home/user/degree-diameter/research/squads/bh5b-r2/c5
for spec in "b22_33 27 1" "b22_33 27 2" "b22_33 35 1" "b22_24 33 1"; do
  set -- $spec
  out=$(D=5 SECS=60 SEED=$3 OUT=sols/L176_$1_$2_$3.txt timeout 150 nice -n 10 ./vl bases/$1.txt grp176/sg_176_$2.txt 2>/dev/null | grep RESULT)
  echo "L 176_$2 $1 seed$3 $out" >> long176.log
done
echo DONE >> long176.log
