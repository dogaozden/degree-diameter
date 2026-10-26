#!/bin/bash
# Screen: haar_fast 4 8 SECS SEED 8 OUT meta m k r 1 ; one line per group
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
SECS=$1; SEED=$2; shift 2
for spec in "$@"; do
  set -- $spec
  N=$1; m=$2; k=$3; r=$4
  tag="m${m}_k${k}_r${r}"
  res=$(THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 $SECS $SEED 8 out_$tag.txt meta $m $k $r 1 2>&1 | grep RESULT | tail -1)
  echo "N=$N meta $m $k $r :: $res"
done
