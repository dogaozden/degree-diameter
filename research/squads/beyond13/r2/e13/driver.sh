#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond13/r2/e13
for g in "psl 7 1567" "psl 13 241" "sl 11 199" "psl 11 397" "sl 5 2179" "psl 23 43" "psl 7 1549"; do
  set -- $g
  nice -n 10 ./orbscan scan $1 $2 $3 14 100 7 out/s_$1_$2_$3 1 >> out/scan.log 2>&1
done
echo ALLDONE >> out/scan.log
