#!/bin/bash
# usage: screen1.sh SECONDS SEED GROUPS... ; runs flift on base33_{0,1,2} for each group
T=/home/user/degree-diameter/research/squads/b48/tools
D=/home/user/degree-diameter/research/squads/b48/r4/h04
S=$1; SEED=$2; shift 2
for g in "$@"; do
  for b in 0 1 2; do
    if [[ $g == *.bin ]]; then G=$D/$g; else G=$g; fi
    tag=$(echo "$g" | tr ':' '_')
    out=$D/runs/${tag}_b$b.out
    line=$(THREADS=1 timeout 120 nice -n 10 $T/flift $D/base33_$b.txt "$G" 3 10 $S $SEED 8 $out 2>&1 | grep RESULT)
    echo "$g base$b $line"
  done
done
