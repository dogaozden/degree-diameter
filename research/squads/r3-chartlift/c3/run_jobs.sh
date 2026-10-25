#!/bin/bash
# usage: run_jobs.sh JOBFILE SECONDS OUTDIR ; JOBFILE lines: "BASE GROUPFILE FLAGS TAG" (absolute paths), run one at a time
JOBS=$1; SECS=$2; OUT=$3; BIN=/home/user/degree-diameter/research/squads/r3-chartlift/c3/ctrl_search
mkdir -p $OUT
while read -r b g fl tag; do
  [ -z "$b" ] && continue
  timeout $((SECS+30)) nice -n 10 $BIN $b $g $fl $SECS 1 $OUT/$tag > $OUT/$tag.out 2>&1
  echo "$tag | $(tail -n 1 $OUT/$tag.out | cut -c1-110)"
done < $JOBS
