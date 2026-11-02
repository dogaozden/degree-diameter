#!/bin/bash
# usage: run.sh SEED  -> one 90 s fresh-seed run, appends to seeds.txt
cd /home/user/degree-diameter/research/squads/raise9/r4/r1
B=/home/user/degree-diameter/research/squads/raise9/bin
S=$1
SAVEBEST=b_s$S.txt THREADS=1 timeout -s KILL 100 nice -n 10 $B/haar_gen3s 6 9 90 $S 16 OUT_s$S.txt meta 1559 41 84 1 > log_s$S.txt 2>&1
rc=$?
R=$(grep '^RESULT' log_s$S.txt | sed -e 's/.*best=\([0-9]*\) evals=\([0-9]*\).*/\1 | \2/')
echo "$S | $R" >> seeds.txt
echo "seed $S rc=$rc $R"
[ -f OUT_s$S.txt ] && echo "FOUND OUT_s$S.txt"
