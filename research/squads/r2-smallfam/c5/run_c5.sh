#!/bin/bash
# Card c5, round r2-smallfam: (3,9), the six 4+4 bases over orders 65-70 (lscreen), then the
# lowest-cost (group, base) pair re-annealed (reanneal_c5.py), then order 64 in time slices.
C5=/home/user/degree-diameter/research/squads/r2-smallfam/c5
SM=/home/user/degree-diameter/research/theorems/smallfam
export THREADS=1 OUTDIR=$C5 SCRATCH=$C5/tmp
mkdir -p "$SCRATCH"
cd "$SM" || exit 1
DEADLINE=$(date -u -d '2026-10-25T05:03:30Z' +%s)   # phase 3 must end by then (20-minute box starts 04:45:09Z)

for b in 0 1 2 3 4 5; do
  timeout 1200 nice -n 10 python3 lscreen.py bases/b44_$b.txt 9 65 70 --secs 4 --abmin 1 --abmax 1000000
  echo "phase1 base $b done $(date -u +%T)"
done
echo "phase1 done $(date -u +%T)"

timeout 400 nice -n 10 python3 "$C5/reanneal_c5.py"
echo "phase2 done $(date -u +%T)"

for k in 0 1 2 3 4 5; do
  left=$(( DEADLINE - $(date +%s) ))
  [ $left -le 5 ] && break
  slice=$(( left / (6 - k) ))
  timeout "$slice" nice -n 10 python3 lscreen.py bases/b44_$k.txt 9 64 64 --secs 4 --abmin 1 --abmax 1000000
  echo "phase3 base $k done $(date -u +%T)"
done
echo "ALL DONE $(date -u +%T)"
