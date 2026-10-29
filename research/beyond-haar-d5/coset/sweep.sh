#!/bin/bash
# usage: sweep.sh ORDER H DELTA [IDS gap list]   results appended to logs/sweep_h<H>_d<DELTA>.txt
order=$1; h=$2; delta=$3; ids=${4:-}
dir=tmp_${order}_${h}; mkdir -p $dir logs
extra=""; [ -n "$ids" ] && extra="IDS:=$ids;"
gap -q -c "ORDER:=$order; H_ORDER:=$h; OUTDIR:=\"$dir\"; $extra" sg_export.g > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  r=$(timeout 300 ./dcenum $f $delta 5 ${f%.dc2}.edges 2000000 2>/dev/null | tail -1)
  echo "$r" >> logs/sweep_h${h}_d${delta}.txt
  case "$r" in *"solutions 0 "*) rm -f ${f%.dc2}.edges ;; *) cp ${f%.dc2}.edges logs/ ; echo "HIT $r" ;; esac
  rm -f $f
done
rm -rf $dir
