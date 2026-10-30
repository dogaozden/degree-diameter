#!/bin/bash
# exhaustive-only screen (SA 0) of the 19 non-solvable groups of order 1200, one at a time
C1=/home/user/degree-diameter/research/squads/bh5-r4/c1
for i in 473 474 475 476 477 478 479 480 481 482 483 484 939 940 941 942 943 944 945; do
  timeout 600 nice -n 10 $C1/drive.sh 1200 $i 0
done
echo ALLDONE > $C1/logs/batch_1200.done
