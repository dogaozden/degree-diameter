#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^ALLS_DONE' out/batch_s2.log)" -ge 1 ]; do sleep 3; done
for s in 19 20 21 22 23 24 25 26; do
  ./run1.sh c170_D5_77d 5 17 4 2,2,2,2,2,2,2,1,1,1 2,2,2,2,2,2,2,1,1,1 40 $s 40 4
done
echo ALLT_DONE
