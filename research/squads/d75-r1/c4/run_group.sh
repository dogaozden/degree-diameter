#!/bin/bash
# usage: run_group.sh ORDER ID SECS "SEEDS"  -- export SmallGroup(ORDER,ID) bi-coset graphs with |H|=2 (non-Haar, core-free),
# anneal every diagonal pair (H=K) with dcenum SA for SECS per seed; appends RESULT lines to results.txt
order=$1; id=$2; secs=$3; seeds=${4:-1}
dir=tmp/g_${order}_${id}; rm -rf $dir; mkdir -p $dir
gap -q -c "ORDER:=$order; H_ORDER:=2; OUTDIR:=\"$dir\"; IDS:=[$id]; SKIPHAAR:=true;" sg_export.g > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  b=$(basename ${f%.dc2}); i=${b##*_}; rest=${b%_*}; j=${rest##*_}
  [ "$i" = "$j" ] || { rm -f $f; continue; }
  for s in $(seq 1 $seeds); do
    out=$dir/${b}_s$s.edges
    r=$(SA=1 SECS=$secs SEED=$s TMPDIR=$PWD/tmp timeout $((secs*4+120)) nice -n 10 ./dcenum $f 7 5 $out 2>/dev/null | tail -1)
    echo "ORD $order ID $id $b seed $s secs $secs :: $r" >> results.txt
    case "$r" in *"best 0 "*) echo "HIT $order $id $b seed $s" >> results.txt; cp $out hits_${order}_${id}_${b}_s$s.edges;; esac
  done
  rm -f $f
done
