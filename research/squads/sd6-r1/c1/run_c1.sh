#!/bin/bash
# c1: self-dual sdhi on metacyclic groups, N ascending, d>=3, inv 0.
S=/home/user/degree-diameter/research/selfdual-d6/src/sdhi
OUT=/home/user/degree-diameter/research/squads/sd6-r1/c1
sed -n "$1,$2p" $OUT/meta_list_2100_2800.txt | while read N m k r d inv; do
  log=$OUT/logs/meta_${m}_${k}_${r}.log
  SECS=${SECS:-15} MAXSOL=1 TYPES=1+2+2+2,1+1+1+2+2 THREADS=1 timeout ${TO:-150} nice -n 10 $S 7 6 meta $m $k $r cyc 1 > $log 2>&1
  echo "N=$N m=$m k=$k r=$r d=$d exit=$? sols=$(grep -c '^SOL' $log)"
done
