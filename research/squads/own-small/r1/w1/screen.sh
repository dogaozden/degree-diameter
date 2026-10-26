#!/bin/bash
# usage: screen.sh SECS OUTFILE GROUPFILE...   (runs thetaS, dumbbell, twoSemi over each group)
S=$1; OUT=$2; shift 2
W=/home/user/degree-diameter/research/squads/own-small/r1/w1
L=/home/user/degree-diameter/research/squads/own-small/tools/bin/lift
for g in "$@"; do
  for b in thetaS dumbbell twoSemi; do
    r=$($L $W/bases/$b.txt $g 3 10 $S 7 2>&1 | grep RESULT | tail -1)
    echo "$b $(basename $g) $r" >> $OUT
  done
done
