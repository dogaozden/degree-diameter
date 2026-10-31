#!/bin/bash
# card c2 sweep: composite metacyclic groups (N 4881..5100, inv<=1, d>=4), all types, ENUM + tabu
cd /home/user/degree-diameter
OUT=research/squads/sdhi-r1/c2/out
while read -r N m k r d inv; do
  f=$OUT/g_${N}_${m}_${k}_${r}.txt
  ENUM=1 ECAP=3000000 NEAR=30 SECS=5 THREADS=1 timeout 90 nice -n 10 research/selfdual-hi/src/sdhi 5 8 meta "$m" "$k" "$r" cyc 1 > "$f" 2>&1
  echo "$N $m $k $r $d $inv rc=$?" >> $OUT/summary.txt
done < research/squads/sdhi-r1/c2/groups.txt
echo SWEEP_DONE >> $OUT/summary.txt
