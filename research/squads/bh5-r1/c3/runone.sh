#!/bin/bash
# usage: runone.sh BASE GROUPFILE SECS SEED T0 T1 TAG  -> appends one line to runs/summary.txt
R=/home/user/degree-diameter/research/beyond-haar-d5
D=/home/user/degree-diameter/research/squads/bh5-r1/c3
cd $D
out=$(SWAP=0.05 SECS=$3 SEED=$4 T0=$5 T1=$6 OUT=runs/$7.sol timeout $(( ${3%.*} + 60 )) nice -n 10 $R/vl $1 $2 2>runs/$7.err | grep RESULT)
echo "$7 base=$1 group=$(basename $2) secs=$3 seed=$4 T0=$5 T1=$6 :: $out" | tee -a runs/summary.txt
