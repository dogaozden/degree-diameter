#!/bin/bash
# chain613.sh: hmeta random-start + chained links at (6,13) on odd-order Frobenius groups just above 20,867,196
cd "$(dirname "$0")"
for g in "564103 37 96076" "509221 41 254461" "485729 43 37495"; do set -- $g; S=""
  for i in 1 2 3 4; do out=rec/c613_$1_$2_$i
    res=$( env ${S:+START=$S} T0=8 T1=1 REHEAT=400 THREADS=1 timeout 300 ./hmeta 6 13 280 $((i * 7 + $2)) 8 $out $1 $2 $3 2>/dev/null | grep RESULT); echo "$out $res"
    case "$res" in *best=0\ *) echo FOUND $out; exit 0;; esac; [ -f $out.best ] && S=$out.best; done; done
