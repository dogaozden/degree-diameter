#!/bin/bash
# usage: screen.sh BASE SECS SEED ORDER...   ; appends "N I best n base" lines to screen.txt
B=$1; S=$2; SEED=$3; shift 3
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/b3
for N in "$@"; do
  for I in $(python3 -c "
import re
for l in open('groups.txt'):
    p=l.split()
    if int(p[0])==$N: print(p[1])"); do
    T=g${N}_${I}.bin
    [ -f $T ] || timeout 120 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T >/dev/null 2>&1
    R=$(timeout $((S+30)) nice -n 10 ../../tools/flift $B $T 7 5 $S $SEED 2>&1 | grep RESULT)
    echo "$N $I $(echo $R | sed 's/.*best=\([0-9]*\).*n=\([0-9]*\).*/best=\1 n=\2/') $B" >> screen.txt
  done
done
