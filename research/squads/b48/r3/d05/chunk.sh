#!/bin/bash
# usage: chunk.sh M K R SLICE START END  -> runs exh_meta lines START..END (1-based) of the given slice through flift (4 9, LIMIT=2)
T=/home/user/degree-diameter/research/squads/b48/tools
M=$1; K=$2; R=$3; SL=$4; A=$5; B=$6
G=meta:$M:$K:$R
python3 $T/exh_meta.py $M $K $R --slice $SL 2>/dev/null | awk -v a=$A -v b=$B 'NR>=a && NR<=b {print} NR>b {exit}' | \
  THREADS=1 LIMIT=2 ONLYLOW=1 timeout 60 nice -n 10 $T/flift $T/bases/dipole4.txt $G 4 9 eval
echo "chunk $M $K $R slice=$SL lines=$A..$B rc=$?"
