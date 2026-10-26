#!/bin/bash
# usage: screen.sh START END  (line numbers of selected.txt); 3 s haar_tab run per group, seed 1, K=16
cd /home/user/degree-diameter/research/squads/hunt-d5/r4/d2
export THREADS=1 OMP_NUM_THREADS=1 SAVEBEST=1
sed -n "$1,$2p" selected.txt | while read N I; do
  T=g${N}_${I}.bin
  [ -f $T ] || timeout 300 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T >/dev/null 2>&1
  R=$(timeout 60 nice -n 10 ../../tools/haar_tab 6 5 3 1 16 s${N}_${I}.sol tab $T 1 2>/dev/null | grep RESULT)
  echo "$N $I $R" | tee -a screen.tsv
done
