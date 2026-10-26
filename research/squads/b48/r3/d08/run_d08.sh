#!/bin/bash
# d08: AGL(1,q) x Z_n Haar screen at D=9 (haar_fast), then 60 s push of the best
cd /home/user/degree-diameter/research/squads/b48/r3/d08
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
for g in "13 16" "11 23" "7 60" "7 61" "7 63" "7 67" "5 125" "5 131" "5 139" "17 10" "19 8" "23 5" "31 3" "37 2" "13 17" "11 25" "3 421" "3 445"; do
  set -- $g
  THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 9 8 1 8 s1_$1_$2.txt agl1 $1 $2 2>&1 | grep RESULT
done
THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 9 60 2 8 p2_23_5.txt agl1 23 5 | grep RESULT
