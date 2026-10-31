#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^ALLP_DONE' out/batch_p.log)" -ge 1 ]; do sleep 3; done
for s in 5 6 7 8; do
  ./run1.sh c170_D5_77b 5 17 4 2,2,2,2,2,2,2,1,1,1 2,2,2,2,2,2,2,1,1,1 40 $s 40 4
done
G=out/c170_D5_77b/s5/grp.txt
./restart.sh c170_D5_115rst out/c170_D5_77b/s5/grp.txt best/n170_D5_7_7_far115.edges 60 1 10 2
echo ALLQ_DONE
