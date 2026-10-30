#!/bin/bash
# usage: sweep.sh ORDER h DELTA SECS "IDS" [SEEDS]  -- every SmallGroup(ORDER, i), i in IDS (GAP list), all pairs of
# classes of core-free subgroups of order h (Haar-type ones dropped: SKIPHAAR:=true), annealing over unions of
# double cosets (dcenum SA) for SECS seconds per seed. One line per (group, H, K, seed) in logs/sw_<order>_h<h>_d<delta>.txt
# (the RESULT line names the .dc2 file: sg<ORDER>_<id>_<i>_<j>); a cost-0 graph is copied to logs/HIT_*.edges;
# cost <= NEAR keeps the .dc2 and the best .edges in logs/near/.
order=$1; h=$2; delta=$3; secs=$4; ids=$5; seeds=${6:-1}; NEAR=${NEAR:-12}
dir=tmp_${order}_${h}_$$; mkdir -p $dir logs logs/near
gap -q -c "ORDER:=$order; H_ORDER:=$h; OUTDIR:=\"$dir\"; IDS:=$ids; SKIPHAAR:=true;" sg_export.g > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  for s in $(seq 1 $seeds); do
    r=$(SA=1 SECS=$secs SEED=$s timeout $((secs*8+600)) nice -n 5 ./dcenum $f $delta 5 ${f%.dc2}_s$s.edges 2>/dev/null | tail -1)
    echo "$r seed $s" >> logs/sw_${order}_h${h}_d${delta}.txt
    b=$(echo "$r" | sed -n 's/.* best \([0-9]*\) .*/\1/p')
    case "$r" in *"best 0 "*) cp ${f%.dc2}_s$s.edges logs/HIT_$(basename ${f%.dc2})_s$s.edges; cp $f logs/; echo "HIT $r";; esac
    if [ -n "$b" ] && [ "$b" -le "$NEAR" ]; then cp $f logs/near/; cp ${f%.dc2}_s$s.edges logs/near/$(basename ${f%.dc2})_s$s.edges 2>/dev/null; fi
  done
  rm -f $f ${f%.dc2}_s*.edges
done
rm -rf $dir
