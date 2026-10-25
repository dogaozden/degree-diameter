#!/bin/bash
# card c3, second default run (seed 2): PSL(2,71) x Z12871, ORBIT="5 3 1", K 4, default schedule, 600 s.
# Then EVAL of its best S (OUT2.txt.best) with UNCPRINT=1, in the same slot hold.
HB=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin/haar_big
cd /home/user/degree-diameter/research/squads/d16D10-r2/c3 || exit 1
s=$(date +%s)
ORBIT="5 3 1" THREADS=1 timeout 660 nice -n 10 $HB 16 10 600 2 4 OUT2.txt psl 71 12871 > run2.out 2> run2.log
echo "rc=$? wall=$(( $(date +%s) - s )) start=$(date -u -d @$s +%T)" > run2.rc
EVAL=OUT2.txt.best UNCPRINT=1 THREADS=1 timeout 300 nice -n 10 $HB 16 10 0 1 1 /dev/null psl 71 12871 > eval2.out 2> eval2.log
echo "rc=$?" > eval2.rc
