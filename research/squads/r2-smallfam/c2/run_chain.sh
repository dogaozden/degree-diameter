#!/bin/bash
# c2: lift screen of bases b33_1 and b33_2 over orders 134..142, alternating base per order, with a hard deadline.
export OUTDIR=/home/user/degree-diameter/research/squads/r2-smallfam/c2
export SCRATCH=/home/user/degree-diameter/research/squads/r2-smallfam/c2/tmp
export THREADS=1
mkdir -p "$SCRATCH"
cd /home/user/degree-diameter/research/theorems/smallfam || exit 1
DEADLINE=$(( $(date +%s) + ${1:-600} ))
for n in 134 135 136 137 138 139 140 141 142; do
  for b in bases/b33_1.txt bases/b33_2.txt; do
    rem=$(( DEADLINE - $(date +%s) ))
    if [ "$rem" -le 0 ]; then echo "DEADLINE reached before order $n $b $(date -u +%T)"; exit 0; fi
    echo "=== $b order $n start $(date -u +%T) remaining ${rem}s"
    timeout "$rem" nice -n 10 python3 lscreen.py "$b" 10 "$n" "$n" --secs 6 --abmin 1 --abmax 1000000
    echo "=== $b order $n end $(date -u +%T) rc=$?"
  done
done
echo CHAIN_DONE $(date -u +%T)
