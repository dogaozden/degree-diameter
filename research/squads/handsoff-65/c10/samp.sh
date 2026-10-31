#!/bin/bash
# samp.sh L NAB K: K random augmentations of quotient base L; EVAL cost of each (random new voltages); prints the min
cd /home/user/degree-diameter/research/squads/handsoff-65/c10
L=$1; NAB=$2; K=$3; M=$(head -1 bases/n$L.tab)
for s in $(seq 1 $K); do
  python3 augment.py bases/q$L.base samp/t.base $NAB $((s+1000)) 1 $M >/dev/null
  c=$(EVAL=1 ../shared/vl samp/t.base bases/n$L.tab 2>/dev/null | tail -1 | awk '{print $3}')
  echo "$c $s"
done | sort -n > samp/L${L}_n${NAB}.txt
head -3 samp/L${L}_n${NAB}.txt; awk '{s+=$1} END {print "mean", s/NR, "count", NR}' samp/L${L}_n${NAB}.txt
