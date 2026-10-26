#!/bin/bash
# usage: screen.sh SECS SEED   (runs all bases x groups below, one at a time)
T=/home/user/degree-diameter/research/squads/b48/tools
D=/home/user/degree-diameter/research/squads/b48/r5/k08
S=$1; SEED=$2
for g in "264 44 6 21" "270 45 6 14" "280 20 14 9" "288 48 6 17" "288 16 18 7" "260 26 10 25" "282 47 6 46" "290 29 10 28"; do
  set -- $g; N=$1; m=$2; k=$3; r=$4
  for b in k01 k02 k03; do
    out=$D/s_${b}_${m}_${k}_${r}.sol
    res=$(NOTREE=1 ODDSTRIDE=$m QUIET=1 THREADS=1 timeout 120 nice -n 10 $T/lift $D/$b.txt meta:$m:$k:$r 3 9 $S $SEED 8 $out | grep RESULT)
    echo "$b N=$N meta $m $k $r :: $res"
  done
done
