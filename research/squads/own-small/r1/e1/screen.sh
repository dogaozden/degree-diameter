#!/bin/bash
# screen.sh BASE SECS OUTFILE GROUPLIST... : one short flift anneal per group (d=3 D=9), append "best group" lines
BASE=$1; SECS=$2; OUT=$3; shift 3
for g in "$@"; do
  r=$(/home/user/degree-diameter/research/squads/own-small/tools/bin/flift $BASE $g 3 9 $SECS 1 2>/dev/null | grep '^RESULT' | sed 's/.*best=\([0-9]*\).*/\1/')
  echo "$r $g" >> $OUT
done
