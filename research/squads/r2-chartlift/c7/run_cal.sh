#!/bin/bash
# usage: run_cal.sh JOBFILE SECONDS OUTDIR   (JOBFILE lines: GROUPFILE TAG); one process at a time; base and flags fixed
C7=/home/user/degree-diameter/research/squads/r2-chartlift/c7
BASE=$C7/k7r1.txt; FLAGS=$C7/k7q2.flags; SECS=$2; OUT=$3; mkdir -p $OUT
while read g tag; do
  timeout 900 nice -n 10 $C7/ctrl_search $BASE $C7/$g $FLAGS $SECS ${SEED:-1} $OUT/$tag > $OUT/$tag.out 2>&1
  echo "$tag $(grep -E 'best_cost' $OUT/$tag.out | tail -n 1)"
done < $1
