#!/bin/bash
# sampdg.sh L NAB K KTOP S0: K damage-guided augmentations (KTOP lowest-damage base edges), keep the least EVAL cost
cd /home/user/degree-diameter/research/squads/handsoff-65/c10
L=$1; NAB=$2; K=$3; KT=$4; S0=$5; M=$(head -1 bases/n$L.tab)
best=999999999
for s in $(seq 1 $K); do
  python3 augdg.py bases/q$L.base samp/d.base $NAB $((s+S0)) $M samp/dmg_L$L.txt $KT
  c=$(EVAL=1 ../shared/vl samp/d.base bases/n$L.tab 2>/dev/null | tail -1 | awk '{print $3}')
  if [ "$c" -lt "$best" ]; then best=$c; cp samp/d.base samp/bestdg_L${L}_n${NAB}.base; fi
done
echo "L$L nab$NAB ktop$KT best start $best"
