#!/bin/bash
# usage: chain.sh NAME SECONDS SEED K m k r [T0]   (continues from NAME.best if present); writes NAME.sol on cost 0
B=/home/user/degree-diameter/research/frontier/beyond13
F=/home/user/degree-diameter/research/squads/beyond13/r3/f07
NAME=$1; SEC=$2; SEED=$3; K=$4; M=$5; KK=$6; R=$7; T0=${8:-2}
cd $F
if [ -s $F/$NAME.best ]; then export START=$F/$NAME.best; fi
T0=$T0 THREADS=1 timeout 105 nice -n 10 $B/meta/hmeta 4 13 $SEC $SEED $K $F/$NAME $M $KK $R > $F/$NAME.s$SEED.log 2>&1
tail -1 $F/$NAME.s$SEED.log
