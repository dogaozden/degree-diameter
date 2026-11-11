#!/bin/bash
# screen.sh SECS SEED NAME... : haar_tab 4 9 on tabs/NAME.bin, appends "NAME SECS SEED best" to screen.tsv
H=/home/user/degree-diameter/research/squads/handsoff-49
SECS=$1; SEED=$2; shift 2
for nm in "$@"; do
  out=$H/w15/runs/${nm}_s${SEED}.out
  best=$(timeout 540 nice -n 10 $H/tools/haar_tab 4 9 $SECS $SEED 8 $out tab $H/w15/tabs/$nm.bin 1 2>/dev/null | grep RESULT | sed 's/.* best=\([0-9]*\).*/\1/')
  echo -e "$nm\t$SECS\t$SEED\t$best" >> $H/w15/screen.tsv
  echo "$nm seed=$SEED best=$best"
done
