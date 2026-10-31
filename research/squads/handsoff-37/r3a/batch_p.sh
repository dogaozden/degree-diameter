#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^ALLO_DONE' out/batch_o.log)" -ge 1 ]; do sleep 3; done
G=out/c170_D5_8_7/s2/grp.txt; S=out/c170_D5_8_7/s2/sa_best.edges
./restart.sh c170_D5_87rst $G $S 60 1 10 2
./restart.sh c170_D5_87rst $G $S 60 2 10 2
./run1.sh c180_D5_77 5 18 4 2,2,2,2,2,2,2,1,1,1,1 2,2,2,2,2,2,2,1,1,1,1 40 3 40 4
./run1.sh c180_D5_77 5 18 4 2,2,2,2,2,2,2,1,1,1,1 2,2,2,2,2,2,2,1,1,1,1 40 4 40 4
echo ALLP_DONE
