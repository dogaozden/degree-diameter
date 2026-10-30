#!/bin/bash
# usage: bc_campaign.sh OUTDIR FILE...   (exhaustive bi-Cayley search, all (a,b), one line per run in OUTDIR/summary.txt)
OUT=$1; shift; mkdir -p $OUT
for f in "$@"; do
  base=$(basename $f .txt)
  for ab in "2 4" "4 2" "3 3" "1 5" "5 1"; do
    set -- $ab
    log=$OUT/${base}_a$1b$2.log
    [ -s $log ] && continue
    A=$1 B=$2 D=5 SECS=${SECS:-1800} MAXSOL=20 EDGES=$OUT/${base}_a$1b$2.best.edges ./tools/bicay $f > $log 2>&1
    echo "$base a=$1 b=$2 | $(head -c 200 $(dirname $f)/$base.name | tr -d '\n') | $(grep RESULT $log)" >> $OUT/summary.txt
  done
done
