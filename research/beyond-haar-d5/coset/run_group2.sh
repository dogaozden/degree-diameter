#!/bin/bash
# usage: run_group2.sh NAME "GAP expr" H DELTA [SA_SECS]  -- dc2 export (fast subgroups, core-free), then for each
# (H, K) pair: exhaustive if at most 2M unions, else annealing (SA_SECS seconds, default 60). Results: logs/NAME_h<H>_d<DELTA>.r2
name=$1; expr=$2; h=$3; delta=$4; secs=${5:-60}
dir=tmp2_${name}_$h; mkdir -p $dir logs
gap -q -c "G:=$expr; H_ORDER:=$h; Read(\"dc2_lib.g\"); ExportPairs(G, H_ORDER, \"$dir/$name\"); QUIT;" > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  r=$(timeout 900 ./dcenum $f $delta 5 ${f%.dc2}.edges 2000000 2>/dev/null | tail -1)
  case "$r" in *"tested 2000000 "*) r="$r || $(SA=1 SECS=$secs timeout $((secs+60)) ./dcenum $f $delta 5 ${f%.dc2}.edges 2>/dev/null | tail -1)";; esac
  echo "$r" | tee -a logs/${name}_h${h}_d${delta}.r2
  case "$r" in *"best 0 "*) cp ${f%.dc2}.edges logs/HIT_$(basename ${f%.dc2}).edges; echo "HIT $r";; esac
done
rm -rf $dir
