#!/bin/bash
# step 2: joint per-edge annealing (mlift_ejoint) from the record echart, one group, one run. usage: run2.sh GROUP SECS SEED
cd /home/user/degree-diameter/research/squads/d12D5-r1/c5
export THREADS=1
G=$1; S=$2; SEED=$3
R=/home/user/degree-diameter/research/d12D5
B=$R/base_k33m.txt
M=$R/mlift_ejoint
E=$R/graphs/d12D5_n10692_k33m_z22e_echart.txt
mkdir -p joint
P=$PWD/joint/${G}_s${SEED}
s=$(date +%s)
WRITEBEST=1 INIT_ECHART=$E timeout 400 nice -n 10 $M $B t_$G.txt $S $SEED 2 0.8 $P > joint/${G}_s${SEED}.log 2>&1
rc=$?
bc=$(grep -o 'best_cost=[0-9]*' joint/${G}_s${SEED}.log | cut -d= -f2)
echo "$G seed=$SEED secs=$S rc=$rc wall=$(( $(date +%s) - s ))s best_cost=${bc:-NA}" >> joint/summary.txt
if [ -n "$bc" ] && [ "$bc" -le 6 ] && [ -f $P.edges ]; then
  python3 $R/elift.py $P.edges $P.echart joint/${G}_s${SEED}_lift.edges > joint/${G}_s${SEED}_elift.log 2>&1
  timeout 600 nice -n 10 $R/apsp joint/${G}_s${SEED}_lift.edges 12 5 > joint/${G}_s${SEED}_apsp.txt 2>&1
  echo "$G seed=$SEED apsp: $(grep -m1 RESULT joint/${G}_s${SEED}_apsp.txt)" >> joint/summary.txt
  rm -f joint/${G}_s${SEED}_lift.edges
fi
echo "DONE $G $SEED" >> joint/summary.txt
