#!/bin/bash
# usage: screen.sh ORDER K SECS SEED ID...   (appends one line per group to runs/screen.log)
D=/home/user/degree-diameter/research/squads/deep-65/round2/h6
O=$1; K=$2; S=$3; SEED=$4; shift 4
for i in "$@"; do
  out=$(timeout 105 nice -n 10 $D/hubtabu $D/groups/sg_${O}_${i}.txt $K tabu $S $SEED - 300 2>&1 | grep -E '^BEST|miss=' | tr '\n' ' ')
  echo "ORD=$O k=$K secs=$S seed=$SEED id=$i [$(cat $D/groups/sg_${O}_${i}.name)] $out" >> $D/runs/screen.log
  echo "ORD=$O k=$K id=$i $(echo $out | sed -n 's/.*cost=\([0-9]*\).*/\1/p')"
done
