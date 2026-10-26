#!/bin/bash
# usage: screen.sh SECONDS SEED OUTDIR  then pairs of "family q n" on stdin
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
SEC=$1; SEED=$2; OUT=$3
while read fam q n; do
  [ -z "$fam" ] && continue
  THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 $SEC $SEED 8 $OUT/${fam}_${q}_${n}.txt $fam $q $n 2>&1 | grep RESULT | sed "s/^/$fam $q $n :: /"
done
