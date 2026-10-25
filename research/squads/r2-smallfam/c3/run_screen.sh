#!/bin/bash
# c3: 4+4 bases over orders 101-106 with lscreen (5 s per group), cube and b44_0 first
export OUTDIR=/home/user/degree-diameter/research/squads/r2-smallfam/c3
export SCRATCH=/home/user/degree-diameter/research/squads/r2-smallfam/c3/tmp
export THREADS=1
mkdir -p "$SCRATCH"
cd /home/user/degree-diameter/research/theorems/smallfam
for b in b44_5 b44_0 b44_1 b44_2 b44_3 b44_4; do
  echo "== start $b $(date +%T)"
  timeout 1200 nice -n 10 python3 lscreen.py bases/$b.txt 10 101 106 --secs 5 --abmin 1 --abmax 1000000
  echo "== end $b rc=$? $(date +%T)"
done
echo "== ALL DONE $(date +%T)"
