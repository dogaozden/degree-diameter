#!/bin/bash
# usage: sweep.sh ORDER h DELTA SECS "IDS" [SEEDS]  -- every SmallGroup(ORDER, i), i in IDS (GAP list), all pairs of
# classes of core-free subgroups of order h (Haar-type ones kept: any valid graph counts); annealing over unions of
# double cosets (dcenum SA) for SECS seconds per seed. One line per (group, H, K, seed) in logs/sw_<order>_h<h>_d<delta>.txt;
# a cost-0 graph is copied to logs/HIT_*.edges.
order=$1; h=$2; delta=$3; secs=$4; ids=$5; seeds=${6:-1}
dir=tmp_${order}_${h}_$$; mkdir -p $dir logs
for id in $(echo "$ids" | tr -d '[]' | tr ',' ' ' | sed 's/\.\./ /g' | awk '{ if (NF==2) { for(i=$1;i<=$2;i++) print i } else for(i=1;i<=NF;i++) print $i }'); do
  timeout 90 gap -q -c "ORDER:=$order; H_ORDER:=$h; OUTDIR:=\"$dir\"; IDS:=[$id]; SKIPHAAR:=true;" sg_export.g >> $dir/gap.log 2>&1 || echo "EXPORT_TIMEOUT_OR_FAIL $order $id" >> logs/sw_${order}_h${h}_d${delta}.txt
done
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  for s in $(seq 1 $seeds); do
    r=$(SA=1 SECS=$secs SEED=$s timeout $((secs*8+600)) nice -n 5 ./dcenum $f $delta 5 ${f%.dc2}_s$s.edges 2>/dev/null | tail -1)
    echo "$r seed $s" >> logs/sw_${order}_h${h}_d${delta}.txt
    case "$r" in *"best 0 "*) cp ${f%.dc2}_s$s.edges logs/HIT_$(basename ${f%.dc2})_s$s.edges; cp $f logs/; echo "HIT $r";; esac
  done
  rm -f $f ${f%.dc2}_s*.edges
done
rm -rf $dir
