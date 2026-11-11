#!/bin/bash
# usage: link.sh NAME SECONDS SEED m k r [START]
B=/home/user/degree-diameter/research/frontier/beyond13
D=/home/user/degree-diameter/research/squads/beyond13/r2/e01/runs
NAME=$1; SEC=$2; SEED=$3; M=$4; K=$5; R=$6; ST=$7
if [ -n "$ST" ]; then export START=$ST; fi
cd $D && THREADS=1 timeout 105 nice -n 10 $B/bin/haar_gen3 4 13 $SEC $SEED 8 $D/$NAME.sol meta $M $K $R 1 > $D/$NAME.s$SEED.log 2>&1
tail -1 $D/$NAME.s$SEED.log
