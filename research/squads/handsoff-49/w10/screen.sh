#!/bin/bash
# usage: screen.sh SECONDS "SEED1 SEED2 ..." NAME...   (haar_tab on tabs/NAME.bin; appends to screen.tsv)
SECS=$1; SEEDS=$2; shift 2
H=/home/user/degree-diameter/research/squads/handsoff-49
cd $H/w10
for name in "$@"; do
  for s in $SEEDS; do
    line=$(THREADS=1 timeout 540 nice -n 10 $H/tools/haar_tab 4 9 $SECS $s 8 runs/${name}_s${s}.sol tab tabs/${name}.bin 1 2>&1 | grep RESULT)
    best=$(echo "$line" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
    echo -e "$name\tseed=$s\tsecs=$SECS\tbest=$best" | tee -a screen.tsv
  done
done
