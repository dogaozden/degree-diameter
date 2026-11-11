#!/bin/bash
# batch.sh TABLE.bin SECS TAG BASE1 BASE2 ... : sequential ltabu runs (one process at a time); prints one line per run
T=$1; S=$2; TAG=$3; shift 3
for B in "$@"; do
  name=$(basename "$B" .base)
  out=$(timeout 540 nice -n 10 env TT=${TT:-8} TTB=${TTB:-20} NOIMP=${NOIMP:-150} KICK=${KICK:-3} QUIET=1 ./ltabu "$T" "$B" 9 "$S" ${SEED:-7} runs/${TAG}_$name 2>/dev/null | grep -E "DONE|RESULT" | tr '\n' ' ')
  echo "$TAG $name $out"
  echo "$TAG $name $out" >> runs/batch_results.txt
done
