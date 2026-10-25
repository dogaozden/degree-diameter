#!/bin/bash
# finish.sh base.in tag : base with structural cost 0 -> nu (zcons + orsolve) -> Z6 lift -> liftcheck -> apsp
set -e
B=$1; T=$2; D=/home/user/degree-diameter/research/d11D5
./plusopt2 $B | head -1 | tee $T.log
SCORE=1 ./plusopt2 $B | grep -q "cost=0 " || { echo "structural cost not 0"; exit 1; }
python3 in2zc.py $B $T.zc
DEDUP=1 MAXOR=12 nice $D/zcons $T.zc $T | grep -E "groups|CONSIST|INCONS|wrote" | tee -a $T.log
NV=$(head -1 $T.zc | awk '{print $2}')
for s in 1 2 3; do
  SEED=$s SA=1 SECS=${SECS:-600} T0=1.0 T1=0.1 nice ./orsolve $T $NV ${T}_nu.txt | tail -1 | tee -a $T.log
  grep -q "best=0 " $T.log && break
done
python3 mklift.py $B ${T}_nu.txt ${T}_lift.txt
$D/liftcheck ${T}_lift.txt 5 | tail -2 | tee -a $T.log
python3 $D/lift2edges.py ${T}_lift.txt ${T}.edges
$D/apsp ${T}.edges 11 5 | tail -3 | tee -a $T.log
