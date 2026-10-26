#!/bin/bash
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
D=/home/user/degree-diameter/research/squads/b48/r1/c03
cd $D
for spec in "1116 186 6 5" "1134 189 6 37" "1176 49 24 19"; do
  set -- $spec
  echo -n "$1 $2 $3 $4 :: "
  THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 40 2 8 ref_$2_$3_$4.txt meta $2 $3 $4 1 2>&1 | grep RESULT
done > refine_log.txt
echo finished >> refine_log.txt
