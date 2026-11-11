#!/bin/bash
# tabu_screen.sh BASE SECS SEED OUT.tsv GROUP... : one tabu run per group (w5)
B=$1; S=$2; SEED=$3; OUT=$4; shift 4
for g in "$@"; do
  r=$(TABU=1 TENURE=12 KICK=300 timeout $((S+60)) nice -n 10 ./tabu "$B" "$g" 4 9 "$S" "$SEED" 8 "out/ts_${SEED}_$(echo $g | tr ':/' '__')" 2>&1 | grep RESULT | sed 's/.*best=\([0-9]*\).*/\1/')
  printf "%s\t%s\t%s\t%s\n" "$B" "$g" "$SEED" "$r" >> "$OUT"
done
