#!/bin/bash
# card c3 (squad d16D10-r2): PSL(2,71) x Z12871, ORBIT="5 3 1", seed 1, K 4, default schedule, 600 s.
# Then EVAL of the best S (OUT.txt.best) with UNCPRINT=1, in the same slot hold (one slot wait instead of two).
HB=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin/haar_big
cd /home/user/degree-diameter/research/squads/d16D10-r2/c3 || exit 1
s=$(date +%s)
ORBIT="5 3 1" THREADS=1 timeout 660 nice -n 10 $HB 16 10 600 1 4 OUT.txt psl 71 12871 > run.out 2> run.log
echo "rc=$? wall=$(( $(date +%s) - s )) start=$(date -u -d @$s +%T)" > run.rc
EVAL=OUT.txt.best UNCPRINT=1 THREADS=1 timeout 300 nice -n 10 $HB 16 10 0 1 1 /dev/null psl 71 12871 > eval.out 2> eval.log
echo "rc=$?" > eval.rc
