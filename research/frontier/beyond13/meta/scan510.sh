#!/bin/bash
# scan510.sh FILE PART NPARTS: hmeta at (5,10) on every PART-th group of FILE (N m k r), 60-s random starts then 2 chained links
cd "$(dirname "$0")"; i=0
while read N m k r; do i=$((i + 1)); [ $(( i % $3 )) -ne $2 ] && continue
  out=rec/s510_${m}_${k}; res=$(env T0=8 T1=1 REHEAT=400 THREADS=1 timeout 70 ./hmeta 5 10 60 $i 8 $out $m $k $r 2>/dev/null | grep RESULT); echo "$N $m $k $res"
  case "$res" in *best=0\ *) echo FOUND $out; continue;; *best=[12]\ *) for l in 1 2; do res=$(env START=$out.best T0=8 T1=1 REHEAT=400 THREADS=1 timeout 100 ./hmeta 5 10 90 $((i * 10 + l)) 8 ${out}_c$l $m $k $r 2>/dev/null | grep RESULT); echo "  chain $l $res"; case "$res" in *best=0\ *) echo FOUND ${out}_c$l; break;; esac; done;; esac
done < $1
