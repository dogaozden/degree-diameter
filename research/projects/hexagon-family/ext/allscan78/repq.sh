#!/bin/bash
# destroy-and-repair (squad r3 c4 repair.py, all non-spread lines): $1 = q, $2 = R, $3 = spread, $4 = start pairs, $5 = bar
cd /home/user/degree-diameter/research/projects/hexagon-family/ext
q=$1; R4=../../../squads/hexfam_r3/c4/repair.py
for s in $(seq 1 80); do
  for k in 1 2 3 4; do
    timeout 400 nice -n 19 python3 $R4 $q $2 $3 $4 allscan78/rep${q}_k${k}_s$s.pairs $s 100000 $k 90 > allscan78/rep${q}_last.log 2>&1
    n=$(cat allscan78/rep${q}_k${k}_s$s.pairs 2>/dev/null | wc -l)
    echo "seed $s nrem $k total $n" >> allscan78/rep$q.log
    [ "$n" -le $5 ] && rm -f allscan78/rep${q}_k${k}_s$s.pairs
  done
done
echo DONE >> allscan78/rep$q.log
