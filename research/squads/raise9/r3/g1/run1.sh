#!/bin/bash
# usage: run1.sh SEED  -- one fresh 90 s haar_gen3s run on meta 1559 41 84, K=8
cd /home/user/degree-diameter/research/squads/raise9/r3/g1
B=/home/user/degree-diameter/research/squads/raise9/bin
S=$1
SAVEBEST=b_s$S.txt THREADS=1 timeout 105 nice -n 10 $B/haar_gen3s 6 9 90 $S 8 OUT_s$S.txt meta 1559 41 84 1 > log_s$S.txt 2>&1
R=$(grep RESULT log_s$S.txt | sed 's/.*best=\([0-9]*\) evals=\([0-9]*\).*/\1 \2/')
echo "$S | 8 | $(echo $R | cut -d' ' -f1) | $(echo $R | cut -d' ' -f2)" >> seeds.txt
if [ -f OUT_s$S.txt ]; then echo "COST0 FOUND seed $S"; fi
tail -1 seeds.txt
