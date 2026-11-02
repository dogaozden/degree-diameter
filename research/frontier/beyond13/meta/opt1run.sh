#!/bin/bash
# opt1run.sh LIST: exhaustive 1-opt (hmeta OPT1) on each near-miss state "N cost file m k r" of LIST, largest N first
cd "$(dirname "$0")"
sort -rn $1 | while read N c f m k r; do out=rec/opt1_${m}_${k}
  res=$(OPT1=1 START=$f THREADS=1 ./hmeta3 5 10 1 1 1 $out $m $k $r 2>/dev/null | grep RESULT); echo "$N $res"
  case "$res" in *best=0\ *) echo FOUND $out;; esac; done
