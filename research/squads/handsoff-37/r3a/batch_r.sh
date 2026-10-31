#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^ALLQ_DONE' out/batch_q.log)" -ge 1 ]; do sleep 3; done
for s in 9 10 11 12 13 14 15 16 17 18; do
  ./run1.sh c170_D5_77c 5 17 4 2,2,2,2,2,2,2,1,1,1 2,2,2,2,2,2,2,1,1,1 40 $s 40 4
done
for s in 5 6 7 8 9 10; do
  ./run1.sh c180_D5_77c 5 18 4 2,2,2,2,2,2,2,1,1,1,1 2,2,2,2,2,2,2,1,1,1,1 40 $s 40 4
done
echo ALLR_DONE
