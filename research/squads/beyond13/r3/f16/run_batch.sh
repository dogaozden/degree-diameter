#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond13/r3/f16
B=/home/user/degree-diameter/research/frontier/beyond13
while read m k r; do
  timeout 100 nice -n 10 ./nlift $B/lifts/bases/gp10_3.txt $m $k $r 13 30 11 g_${m}_${k}_${r} 4 0.3 >> batch_D13.log 2>&1
done < groups.txt
echo DONE >> batch_D13.log
