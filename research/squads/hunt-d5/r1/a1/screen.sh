#!/bin/bash
# Card a1 screen: every non-abelian group of order 193..207, one 3 s anneal (seed 1) each.
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/a1
export OMP_NUM_THREADS=1 THREADS=1
: > screen.txt
for N in $(seq 193 207); do
  timeout 60 nice -n 10 python3 ../../tools/gapgroup.py list $N 2>/dev/null | awk '$3=="false"{print $2}' | while read I; do
    B=g${N}_${I}.bin
    [ -f "$B" ] || timeout 120 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $B >/dev/null 2>&1
    R=$(timeout 60 nice -n 10 ../../tools/haar5 anneal $B 5 3 1 2>/dev/null | grep RESULT)
    BEST=$(echo "$R" | sed -n 's/.* best=\([0-9]*\).*/\1/p')
    echo "$N $I best=$BEST | $(echo "$R" | sed -n 's/.* S= //p')" >> screen.txt
  done
done
echo DONE >> screen.txt
