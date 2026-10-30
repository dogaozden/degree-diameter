#!/bin/bash
# usage: sweep_diag.sh ORDER h DELTA SECS "IDS"  -- like sweep.sh, but only H = K (the same class of core-free
# subgroups on both sides, as for the 384-vertex (5,5) graph); one seed. Lines in logs/sd_<order>_h<h>_d<delta>.txt
order=$1; h=$2; delta=$3; secs=$4; ids=$5
dir=tmpd_${order}_${h}_$$; mkdir -p $dir logs
gap -q -c "ORDER:=$order; H_ORDER:=$h; OUTDIR:=\"$dir\"; IDS:=$ids;" sg_export.g > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  b=$(basename $f .dc2); a=$(echo $b | awk -F_ '{print $(NF-1)}'); c=$(echo $b | awk -F_ '{print $NF}')
  if [ "$a" = "$c" ]; then
    r=$(SA=1 SECS=$secs SEED=1 timeout $((secs*8+600)) nice -n 5 ./dcenum $f $delta 5 ${f%.dc2}.edges 2>/dev/null | tail -1)
    echo "$r" >> logs/sd_${order}_h${h}_d${delta}.txt
    case "$r" in *"best 0 "*) cp ${f%.dc2}.edges logs/HIT_$b.edges; cp $f logs/; echo "HIT $r";; esac
  fi
  rm -f $f ${f%.dc2}.edges
done
rm -rf $dir
