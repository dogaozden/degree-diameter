#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^ALLR_DONE' out/batch_r.log)" -ge 1 ]; do sleep 3; done
./restart.sh c170_D5_60rst out/c170_D5_77b/s7/grp.txt best/n170_D5_7_7_far60.edges 60 1 10 2
./restart.sh c170_D5_60rst out/c170_D5_77b/s7/grp.txt best/n170_D5_7_7_far60.edges 60 2 6 1.5
echo ALLS_DONE
