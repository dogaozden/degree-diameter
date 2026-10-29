#!/bin/bash
# c2 driver3: rerun h=4 orders 728, 744, 736 that produced no RESULT lines during the dc2_lib.g bug window, official sweep.sh
C=/home/user/degree-diameter/research/beyond-haar-d5/coset
P=/home/user/degree-diameter/research/squads/bh5-r3/c2/progress.txt
cd $C
for o in 728 744 736; do
  echo "START3 $o 4 $(date +%T)" >> $P
  timeout 240 nice -n 10 ./sweep.sh $o 4 5
  echo "END3 $o rc=$? $(date +%T)" >> $P
  rm -rf tmp_${o}_4
done
echo ALLDONE3 $(date +%T) >> $P
