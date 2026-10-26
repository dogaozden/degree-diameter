#!/bin/bash
# usage: screen.sh BASE SECS SEED LISTFILE OUTTSV  (LISTFILE: lines "spec N inv ...")
T=/home/user/degree-diameter/research/squads/b48/tools
BASE=$1; SECS=$2; SEED=$3; LIST=$4; OUT=$5; D=${D:-9}
while read spec N inv rest; do
  [ -z "$spec" ] && continue
  line=$(THREADS=1 timeout 120 nice -n 10 $T/flift $BASE $spec 4 $D $SECS $SEED 2>/dev/null | grep RESULT)
  best=$(echo "$line" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  printf "%s\t%s\t%s\t%s\t%s\n" "$(basename $BASE)" "$spec" "$N" "$inv" "${best:-NA}" >> $OUT
done < $LIST
