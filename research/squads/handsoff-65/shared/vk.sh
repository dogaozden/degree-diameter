#!/bin/bash
# usage: vk.sh BASE GROUP OUTDIR SEEDS SECS [KMAXCOST]  (run from research/s65)
# anneal a voltage lift with vl, then run the exact 2-opt search kopt (K=2) on every run whose cost is <= KMAXCOST.
B=$1; G=$2; O=$3; NS=$4; S=$5; KM=${6:-6}; mkdir -p $O
for s in $(seq 1 $NS); do
  sol=$O/$(basename $G .txt)_$(basename $B .txt)_s$s.sol
  c=$(D=5 SECS=$S SEED=$s OUT=$sol timeout $((S*4+60)) nice -n 5 ./tools/vl $B $G 2>/dev/null | grep RESULT | awk '{print $3}')
  k=""
  if [ -n "$c" ] && [ "$c" -le "$KM" ] && [ "$c" -gt 0 ]; then
    timeout 900 nice -n 5 ./tools/kopt $sol $G 2 5 > $sol.k2 2> $sol.k2err; k="k2found $(grep -c '^SOL' $sol.k2)"
  fi
  echo "$(basename $G .txt) $(basename $B .txt) seed $s cost $c $k" | tee -a $O/summary.txt
done
