#!/bin/bash
# Sequential runs for card c2. One lift3 process at a time, each under timeout 900 nice -n 15.
S=/home/user/degree-diameter/research/squads/d10D8-r1/c2
cd /home/user/degree-diameter/research/d10D8/hex || exit 1
run() {
  name=$1; q=$2; shift 2
  start=$(date +%s)
  env "$@" timeout 900 nice -n 15 ./lift3 "$q" > "$S/$name.out" 2> "$S/$name.log"
  rc=$?
  echo "$name rc=$rc secs=$(( $(date +%s) - start )) $(cat "$S/$name.out" 2>/dev/null)" >> "$S/batch2_summary.txt"
}
run q3_cyc20_mc14_s1 3 GROUP="cyc 20" J=2 D=8 MCONST=1 T="1 4" SRC=0 ITERS=1000 SEED=1 OUT="$S/q3_cyc20_mc14_s1.sol"
run q3_cyc30_mc14_s1 3 GROUP="cyc 30" J=2 D=8 MCONST=1 T="1 4" SRC=0 ITERS=1000 SEED=1 OUT="$S/q3_cyc30_mc14_s1.sol"
run q3_cyc40_mc14_s1 3 GROUP="cyc 40" J=2 D=8 MCONST=1 T="1 4" SRC=0 ITERS=1000 SEED=1 OUT="$S/q3_cyc40_mc14_s1.sol"
echo BATCH2_DONE >> "$S/batch2_summary.txt"
