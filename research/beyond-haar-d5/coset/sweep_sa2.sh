#!/bin/bash
# usage: sweep_nh.sh ORDER h DELTA SA_SECS "IDS"  -- SmallGroups of ORDER (IDS: GAP list), Haar-type subgroups skipped,
# exhaustive up to 2M unions else annealing. Appends to logs/sweepsa_<order>_h<h>_d<delta>.txt
order=$1; h=$2; delta=$3; secs=$4; ids=$5
dir=tmpsb_${order}_${h}_$$; mkdir -p $dir logs
gap -q -c "ORDER:=$order; H_ORDER:=$h; OUTDIR:=\"$dir\"; IDS:=$ids;" sg_export.g > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  r=$(timeout 600 ./dcenum $f $delta 5 ${f%.dc2}.edges 500000 2>/dev/null | tail -1)
  case "$r" in *"tested 500000 "*) r="$r || $(SA=1 SECS=$secs timeout $((secs+60)) ./dcenum $f $delta 5 ${f%.dc2}.edges 2>/dev/null | tail -1)";; esac
  echo "$r" >> logs/sweepsa_${order}_h${h}_d${delta}.txt
  case "$r" in *"best 0 "*) cp ${f%.dc2}.edges logs/HIT_$(basename ${f%.dc2}).edges; echo "HIT $r";; esac
  rm -f $f ${f%.dc2}.edges
done
rm -rf $dir
