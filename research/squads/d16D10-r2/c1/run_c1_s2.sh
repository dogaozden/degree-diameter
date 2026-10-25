#!/bin/bash
# card c1 (squad d16D10-r2), second run: same group and schedule as run 1, seed 2. EVAL of its best S in the same slot.
HB=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin/haar_big
cd /home/user/degree-diameter/research/squads/d16D10-r2/c1 || exit 1
s=$(date +%s)
ORBIT="5 3 1" THREADS=1 timeout 660 nice -n 10 $HB 16 10 600 2 4 OUT_s2.txt psl 31 154571 > run_s2.out 2> run_s2.log
echo "rc=$? wall=$(( $(date +%s) - s ))" > run_s2.rc
ORBIT="5 3 1" EVAL=OUT_s2.txt.best UNCPRINT=1 THREADS=1 timeout 300 nice -n 10 $HB 16 10 0 1 1 /dev/null psl 31 154571 > eval_s2.out 2> eval_s2.log
echo "rc=$?" > eval_s2.rc
