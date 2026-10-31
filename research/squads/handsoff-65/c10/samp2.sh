#!/bin/bash
# samp2.sh L NAB K SEED0: keep the augmentation with the least EVAL cost out of K random ones -> samp/best_L_n.base
cd /home/user/degree-diameter/research/squads/handsoff-65/c10
L=$1; NAB=$2; K=$3; S0=$4; M=$(head -1 bases/n$L.tab)
best=999999999
for s in $(seq 1 $K); do
  python3 augment.py bases/q$L.base samp/c.base $NAB $((s+S0)) 1 $M >/dev/null
  c=$(EVAL=1 ../shared/vl samp/c.base bases/n$L.tab 2>/dev/null | tail -1 | awk '{print $3}')
  if [ "$c" -lt "$best" ]; then best=$c; cp samp/c.base samp/best_L${L}_n${NAB}.base; fi
done
echo "best start $best"
