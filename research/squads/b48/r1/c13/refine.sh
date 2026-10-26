#!/bin/bash
# c13 refine: 40 s runs (seed 2, K=8) on the three best screened groups
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r1/c13
for spec in "13 7" "16 5" "11 10"; do
  set -- $spec
  q=$1; n=$2
  echo "== agl1 $q x $n 40s seed 2"
  THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 40 2 8 ref_agl1_${q}_${n}.txt agl1 $q $n 2>&1 | grep RESULT
done
