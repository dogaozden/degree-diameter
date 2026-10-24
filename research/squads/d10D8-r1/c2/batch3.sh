#!/bin/bash
# q=4 structured m=20 with a larger source sample (500 of 2730), started after batch2 finishes.
S=/home/user/degree-diameter/research/squads/d10D8-r1/c2
cd /home/user/degree-diameter/research/d10D8/hex || exit 1
start=$(date +%s)
GROUP="cyc 20" J=2 D=8 MCONST=1 T="1 4" SRC=500 ITERS=1200 SEED=3 OUT="$S/q4_cyc20_mc14_src500_s3.sol" timeout 900 nice -n 15 ./lift3 4 > "$S/q4_cyc20_mc14_src500_s3.out" 2> "$S/q4_cyc20_mc14_src500_s3.log"
rc=$?
echo "q4_cyc20_mc14_src500_s3 rc=$rc secs=$(( $(date +%s) - start )) $(cat "$S/q4_cyc20_mc14_src500_s3.out" 2>/dev/null)" >> "$S/batch3_summary.txt"
echo BATCH3_DONE >> "$S/batch3_summary.txt"
