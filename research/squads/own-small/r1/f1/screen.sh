#!/bin/bash
# screen.sh OUT SECS_PER_RUN BUDGET_SECS SEED LISTFILE   (LISTFILE lines: "BASE GROUPBIN TAG")
# runs flift d=4 D=8 for each line, appends "TAG BASE best=.. n=.." to OUT, stops when BUDGET_SECS is used up
OUT=$1; S=$2; BUD=$3; SEED=$4; LIST=$5
FL=/home/user/degree-diameter/research/squads/own-small/tools/bin/flift
T0=$(date +%s)
while read BASE GB TAG; do
  el=$(( $(date +%s) - T0 )); [ $el -ge $BUD ] && break
  r=$($FL $BASE $GB 4 8 $S $SEED 2>/dev/null | grep RESULT)
  b=$(echo "$r" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  echo "$TAG $(basename $BASE .txt) best=$b" >> $OUT
done < $LIST
echo DONE >> $OUT
