#!/bin/bash
# batch192.sh GROUP K SECS SEED0 COUNT: short breakout lift runs with consecutive seeds; appends to out/batch_<GROUP>_k<K>.tsv
cd "$(dirname "$0")"
G=$1; K=$2; SECS=$3; S0=$4; CNT=$5
OUT=out/batch_${G}_k${K}.tsv
for ((s=S0; s<S0+CNT; s++)); do
  POOL=8 PP=60 STALL=1500 FR=1 TEN=4 WCAP=16 nice -n 10 ./lift3 groups/$G.txt $K $s $SECS out/b_${G}_k${K}_s$s > /dev/null 2> out/b_${G}_k${K}_s$s.log
  R=$(grep "^END" out/b_${G}_k${K}_s$s.log | sed 's/.*best_raw=\([0-9]*\) far=\([0-9]*\).*/\1\t\2/')
  printf 'seed%s\t%s\t%s\n' "$s" "$G" "$R" >> $OUT
  rm -f out/b_${G}_k${K}_s$s.log
done
echo DONE >> $OUT
