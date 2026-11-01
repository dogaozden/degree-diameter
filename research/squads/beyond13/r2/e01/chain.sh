#!/bin/bash
# usage: chain.sh NAME SECONDS SEED M K R   (continues from runs/NAME.sol.best if it exists)
E=/home/user/degree-diameter/research/squads/beyond13/r2/e01
D=$E/runs
NAME=$1; SEC=$2; SEED=$3; M=$4; K=$5; R=$6
cd $D
if [ -s $D/$NAME.sol.best ]; then export START=$D/$NAME.sol.best; fi
THREADS=1 timeout 105 nice -n 10 $E/haar_chain 4 13 $SEC $SEED 8 $D/$NAME.sol meta $M $K $R 1 > $D/$NAME.s$SEED.log 2>&1
tail -2 $D/$NAME.s$SEED.log
