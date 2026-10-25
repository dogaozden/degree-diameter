#!/bin/bash
# usage: joint_run.sh BASE TABLE SEED TAG   (one real joint annealer run with per-edge charts, then check if cost 0)
D=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r1/c3
BASE=$1; TABLE=$2; SEED=$3; TAG=$4
cd $C/runs
P=$C/runs/${TAG}_s${SEED}
INIT_CHART=$D/graphs/d12D5_n9720_k33m_z20_chart.txt THREADS=1 timeout 500 nice -n 10 $D/mlift_ejoint $BASE $TABLE 300 $SEED 2 0.8 $P > $P.log 2>&1
grep best_cost $P.log
if grep -q "best_cost=0 " $P.log; then
  python3 $D/elift.py $P.edges $P.echart $P.lift.edges && $D/apsp $P.lift.edges 12 5 > $P.apsp.txt 2>&1
  grep -h "RESULT" $P.apsp.txt
  rm -f $P.lift.edges
fi
