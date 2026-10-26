#!/bin/bash
# usage: run_jobs.sh JOBFILE SECS SEED ; each line: BASE N I
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/c4
export OMP_NUM_THREADS=1 THREADS=1
while read base N I; do
  [ -z "$base" ] && continue
  T=g${N}_${I}.bin
  if [ ! -f "$T" ]; then
    timeout 120 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T >/dev/null 2>&1 || { echo "$base $N $I TABFAIL" >> results.log; continue; }
  fi
  R=$(timeout 60 nice -n 10 ../../tools/flift $base.base $T 9 5 $2 $3 2>&1 | grep RESULT)
  echo "$base $N $I seed=$3 secs=$2 :: $R" >> results.log
done < "$1"
echo DONE >> results.log
