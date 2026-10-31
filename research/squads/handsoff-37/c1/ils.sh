#!/bin/bash
# iterated tabu: kick the current best with K random 2-switches, tabu (MODE 0, TT 40) for TL CPU-seconds, accept if <=.
# usage: ils.sh START ROUNDS K TL SEED TAG
START=$1; R=$2; K=$3; TL=$4; SEED=$5; TAG=$6
cp "$START" out/${TAG}_cur.edges
best=$(../bin/score37 out/${TAG}_cur.edges | sed 's/.*far=\([0-9]*\).*/\1/')
echo "start far=$best"
for r in $(seq 1 $R); do
  nice -n 10 ./perturb out/${TAG}_cur.edges $K $((SEED*1000+r)) out/${TAG}_kick.edges
  nice -n 10 timeout 300 ./tabu3 out/${TAG}_kick.edges 1000000 40 $((SEED*1000+r)) out/${TAG}_t $K $TL > /dev/null 2> logs/${TAG}_r$r.log
  f=$(../bin/score37 out/${TAG}_t_best.edges | sed 's/.*far=\([0-9]*\).*/\1/')
  if [ "$f" -le "$best" ]; then best=$f; cp out/${TAG}_t_best.edges out/${TAG}_cur.edges; fi
  echo "round $r kicked-result far=$f current-best=$best"
  if [ "$best" -eq 0 ]; then break; fi
done
cp out/${TAG}_cur.edges out/${TAG}_final.edges
echo "final far=$best"
