#!/bin/bash
# destroy-and-repair (squad r3 c4 repair.py, all non-spread lines) from the q = 8 233 state
cd /home/user/degree-diameter/research/projects/hexagon-family/ext
S=../../../d10D7/sets; R4=../../../squads/hexfam_r3/c4/repair.py
for s in $(seq 1 60); do
  for k in 1 2 3; do
    timeout 400 nice -n 19 python3 $R4 8 $S/P8_r5c4_217.txt $S/L8_spread513.txt ../sets/P8_mix233.pairs allscan78/rep8_k${k}_s$s.pairs $s 100000 $k 120 > allscan78/rep8_last.log 2>&1
    n=$(cat allscan78/rep8_k${k}_s$s.pairs 2>/dev/null | wc -l)
    echo "seed $s nrem $k total $n" >> allscan78/rep8.log
    [ "$n" -le 233 ] && rm -f allscan78/rep8_k${k}_s$s.pairs
  done
done
echo DONE >> allscan78/rep8.log
