#!/bin/bash
# scan410.sh: hmeta 20-s random starts at (4,10) on every metacyclic group of g410.txt (N m k r fpf)
cd "$(dirname "$0")"
tail -n +2 g410.txt | while read N m k r f; do for s in 1 2; do out=rec/s410_${m}_${k}_$s
  res=$(env T0=8 T1=1 REHEAT=400 THREADS=1 timeout 40 ./hmeta 4 10 20 $s 16 $out $m $k $r 2>/dev/null | grep RESULT); echo "$N $m $k fpf=$f $res"
  case "$res" in *best=0\ *) echo FOUND $out;; esac; done; done
