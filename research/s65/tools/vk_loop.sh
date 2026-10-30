#!/bin/bash
# usage: vk_loop.sh OUTDIR SECS KMAXCOST ROUNDS GROUP...   (run from research/s65): cycles vk.sh over the groups and
# the three 2+2 bases, one seed block per round; summary lines in OUTDIR/summary.txt, cost-0 graphs in *.sol.k2 files.
O=$1; S=$2; KM=$3; R=$4; shift 4
for r in $(seq 1 $R); do for g in "$@"; do for b in 1 2 3; do
  sol=$O/$(basename $g .txt)_b22_${b}_r$r.sol
  c=$(D=5 SECS=$S SEED=$((r*1000+b)) OUT=$sol timeout $((S*4+60)) nice -n 5 ./tools/vl bases/b22_$b.txt $g 2>/dev/null | grep RESULT | awk '{print $3}')
  k=""
  if [ -n "$c" ] && [ "$c" -le "$KM" ] && [ "$c" -gt 0 ]; then
    timeout 900 nice -n 5 ./tools/kopt $sol $g 2 5 > $sol.k2 2> $sol.k2err; n=$(grep -c '^SOL' $sol.k2); k="k2found $n"
    [ "$n" -gt 0 ] && echo "HIT $sol" >> $O/HITS.txt
  fi
  [ "$c" = "0" ] && echo "HIT0 $sol" >> $O/HITS.txt
  echo "$(basename $g .txt) b22_$b r $r cost $c $k" >> $O/summary.txt
done; done; done
