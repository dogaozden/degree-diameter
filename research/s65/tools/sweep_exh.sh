#!/bin/bash
# usage: sweep_exh.sh ORDER h DELTA SECS "IDS"  -- like sweep.sh, but every (group, H, K) is first enumerated
# exhaustively (all unions of double cosets of total degree DELTA, up to 2M unions); only if that cap is hit, SECS
# seconds of annealing follow. Lines in logs/sx_<order>_h<h>_d<delta>.txt ("tested N" < 2000000 = exhaustive).
order=$1; h=$2; delta=$3; secs=$4; ids=$5
dir=tmpx_${order}_${h}_$$; mkdir -p $dir logs
gap -q -c "ORDER:=$order; H_ORDER:=$h; OUTDIR:=\"$dir\"; IDS:=$ids;" sg_export.g > $dir/gap.log 2>&1
for f in $dir/*.dc2; do
  [ -e "$f" ] || continue
  r=$(timeout 7200 nice -n 5 ./dcenum $f $delta 5 ${f%.dc2}.edges 2000000 2>/dev/null | tail -1)
  case "$r" in *"tested 2000000 "*) r="$r || $(SA=1 SECS=$secs SEED=1 timeout $((secs*8+600)) ./dcenum $f $delta 5 ${f%.dc2}.edges 2>/dev/null | tail -1)";; esac
  echo "$r" >> logs/sx_${order}_h${h}_d${delta}.txt
  case "$r" in *"best 0 "*) cp ${f%.dc2}.edges logs/HIT_$(basename ${f%.dc2}).edges; cp $f logs/; echo "HIT $r";; esac
  rm -f $f ${f%.dc2}.edges
done
rm -rf $dir
