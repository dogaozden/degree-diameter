#!/bin/bash
# usage: run.sh NAME MODE(t|p|lo) START(-|file) SEED K SECS M KK R
# t = TFULL=1 TARGP=100 ; p = plain ; lo = plain with TMAX=0.6
B=/home/user/degree-diameter/research/squads/beyond11b/bin
D=/home/user/degree-diameter/research/squads/beyond11b/r6/l06
NAME=$1; MODE=$2; ST=$3; SEED=$4; KK=$5; SECS=$6; M=$7; K=$8; R=$9
cd $D
TAG=${NAME}_s${SEED}_K${KK}
ENVS="THREADS=1 SAVEBEST=$D/$TAG.best"
[ "$ST" != "-" ] && ENVS="$ENVS START=$D/$ST"
[ "$MODE" = "t" ] && ENVS="$ENVS TFULL=1 TARGP=100"
[ "$MODE" = "lo" ] && ENVS="$ENVS TMAX=0.6"
[ "$MODE" = "hot" ] && ENVS="$ENVS TMAX=3.0 TMIN=0.3"
env $ENVS timeout 105 nice -n 10 $B/haar_gen3t 6 11 $SECS $SEED $KK $D/$TAG.sol meta $M $K $R 1 > $D/$TAG.log 2>&1
BEST=$(grep '^RESULT' $D/$TAG.log | tail -1 | sed -n 's/.*best=\([0-9]*\).*/\1/p')
echo "$(date +%T) $TAG mode=$MODE start=$ST group=meta $M $K $R N=$((M*K)) best=${BEST:-NA} sol=$([ -f $D/$TAG.sol ] && echo yes || echo no)" >> $D/runs.txt
grep '^RESULT' $D/$TAG.log | tail -1
