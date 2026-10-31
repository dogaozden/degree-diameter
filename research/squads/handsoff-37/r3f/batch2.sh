#!/bin/bash
# batch2.sh GROUP K SECS SEED0 COUNT: short breakout lift runs (lift3 defaults as in r3c), consecutive seeds.
# Results: out/batch2_<GROUP>_k<K>.tsv (seed, raw, far from the lift3 END line); files out/c_<GROUP>_k<K>_s<seed>_best.edges
cd "$(dirname "$0")"
G=$1; K=$2; SECS=$3; S0=$4; CNT=$5
OUT=out/batch2_${G}_k${K}.tsv
for ((s=S0; s<S0+CNT; s++)); do
  LOG=out/c_${G}_k${K}_s$s.log
  POOL=8 PP=60 STALL=1500 FR=1 TEN=4 WCAP=16 nice -n 10 ./lift3 groups/$G.txt $K $s $SECS out/c_${G}_k${K}_s$s > $LOG 2>&1
  R=$(grep "^END" $LOG | sed 's/.*best_raw=\([0-9]*\) far=\([0-9]*\).*/\1\t\2/')
  printf 'seed%s\t%s\t%s\n' "$s" "$G" "$R" >> $OUT
done
echo DONE >> $OUT
