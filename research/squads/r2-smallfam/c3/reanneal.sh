#!/bin/bash
# usage: reanneal.sh BASENAME N I   (e.g. b44_5 103 1 for the best pair found by the screen)
# re-anneal one (group, base) pair with lanneal for 60 s, seeds 2 and 3; writes OUT files into c3/ on cost 0
export OUTDIR=/home/user/degree-diameter/research/squads/r2-smallfam/c3
export SCRATCH=/home/user/degree-diameter/research/squads/r2-smallfam/c3/tmp
export THREADS=1
mkdir -p "$SCRATCH"
b=$1; n=$2; i=$3
cd /home/user/degree-diameter/research/theorems/smallfam
read STRUCT TAB < <(python3 -c "
import sys; sys.path.insert(0,'.')
from screen import export_table
s,t=export_table($n,$i); print(s.replace(' ','_'), t)")
echo "group $n $i $STRUCT table $TAB"
for s in 2 3; do
  timeout 300 nice -n 10 ./lanneal "$TAB" bases/$b.txt 10 60 $s 8 "$SCRATCH/re_${b}_${n}_${i}_s${s}.sol" | tee "$OUTDIR/reanneal_${b}_${n}_${i}_s${s}.log" | grep -E "^RESULT"
done
cp "$TAB" "$SCRATCH/keep_table_${n}_${i}.txt" 2>/dev/null
echo "== reanneal done $(date +%T)"
