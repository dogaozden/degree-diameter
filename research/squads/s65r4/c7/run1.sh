#!/bin/bash
# usage: run1.sh GROUP_ID BASE_NUM SECS SEED  (GROUP_ID like 176_26)
G=$1; B=$2; S=$3; SEED=$4
T=/home/user/degree-diameter
DIR=/home/user/degree-diameter/research/squads/s65r4/c7
TAG=g${G}_b${B}_s${SEED}_t${S}
cd "$DIR"
SECS=$S SEED=$SEED INIT=random timeout $((S+60)) nice -n 10 $T/research/s65/tools/tabu $T/research/s65/bases/b22_${B}.txt $T/research/s65/groups/sg/sg_${G}.txt $DIR/$TAG.sol > $DIR/$TAG.out 2> $DIR/$TAG.err
RES=$(grep RESULT $DIR/$TAG.out | head -1)
echo "$TAG $RES" >> $DIR/summary.txt
