#!/bin/bash
# batch3.sh TAG GROUP K SECS SEED0 COUNT: like batch2.sh but the lift3 knobs come from the caller's environment
cd "$(dirname "$0")"
TAG=$1; G=$2; K=$3; SECS=$4; S0=$5; CNT=$6
OUT=out/batch3_${TAG}.tsv
for ((s=S0; s<S0+CNT; s++)); do
  LOG=out/d_${TAG}_s$s.log
  POOL=${POOL:-8} PP=${PP:-60} STALL=${STALL:-1500} FR=${FR:-1} TEN=${TEN:-4} WCAP=${WCAP:-16} nice -n 10 ./lift3 groups/$G.txt $K $s $SECS out/d_${TAG}_s$s > $LOG 2>&1
  R=$(grep "^END" $LOG | sed 's/.*best_raw=\([0-9]*\) far=\([0-9]*\).*/\1\t\2/')
  printf 'seed%s\t%s\t%s\n' "$s" "$TAG" "$R" >> $OUT
  rm -f $LOG
done
echo DONE >> $OUT
