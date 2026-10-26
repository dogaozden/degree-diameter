#!/bin/bash
# c13 screen: AGL(1,q) x Z_n, haar_fast d=4 D=8, 10 s each, seed 1, K=8
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r1/c13
for spec in "11 10" "5 55" "7 27" "8 20" "9 16" "16 5" "4 92" "3 183" "13 7"; do
  set -- $spec
  q=$1; n=$2
  echo "== agl1 $q x $n" 
  THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 10 1 8 scr_agl1_${q}_${n}.txt agl1 $q $n 2>&1 | grep RESULT
done
