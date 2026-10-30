#!/bin/bash
# usage: batch.sh ORDER "IDS" SECS SEED -- one GAP export for all IDS of ORDER (|H|=2, core-free, non-Haar; diagonal H=K only),
# then dcenum SA (DELTA 7, D 5) for SECS each. Results appended to results.txt; HIT copies to hits/.
order=$1; ids=$2; secs=$3; seed=${4:-1}
dir=tmp/b_${order}_$$; rm -rf $dir; mkdir -p $dir hits
gap -q -c "ORDER:=$order; H_ORDER:=2; OUTDIR:=\"$dir\"; IDS:=$ids; SKIPHAAR:=true;" sg_export.g > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  b=$(basename ${f%.dc2}); i=${b##*_}; rest=${b%_*}; j=${rest##*_}
  [ "$i" = "$j" ] || { rm -f $f; continue; }
  out=hits/${b}_s$seed.edges
  r=$(SA=1 SECS=$secs SEED=$seed TMPDIR=$PWD/tmp timeout $((secs*4+120)) nice -n 10 ./dcenum $f 7 5 $out 2>/dev/null | tail -1)
  echo "ORD $order $b seed $seed secs $secs :: $r" >> results.txt
  case "$r" in *"best 0 "*) echo "HIT $b" >> results.txt;; *) rm -f $out;; esac
  rm -f $f
done
rm -rf $dir
