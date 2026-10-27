#!/bin/bash
# usage: run_batch.sh K LIST.tsv OUT.tsv   (one haar_sym RANDORB=${RANDN:-3000} screen per line, strictly sequential)
K=$1; LIST=$2; OUT=$3; BIN=/home/user/degree-diameter/research/structured/haar_sym
KMF=""; case $K in 3) KMF="3 3 1";; 5) KMF="5 2 0";; esac
: > "$OUT"
while IFS=$'\t' read -r N TAG SPEC; do
  # shellcheck disable=SC2086
  RES=$(THREADS=1 ORBIT="$KMF" RANDORB=${RANDN:-3000} timeout 900 nice -n 15 $BIN 10 8 1 1 8 /dev/null $SPEC 2>/tmp/claude-0/c5_err.txt)
  LINE=$(echo "$RES" | grep "^RANDORB d=" | head -1)
  if [ -z "$LINE" ]; then ERR=$(tail -1 /tmp/claude-0/c5_err.txt 2>/dev/null | tr -d '\t'); printf "%s\t%s\tFAILED\t%s\n" "$N" "$SPEC" "$ERR" >> "$OUT"; continue; fi
  FIX=$(echo "$LINE" | sed -n 's/.*fix=\([0-9]*\).*/\1/p'); MIN=$(echo "$LINE" | sed -n 's/.* min=\([0-9]*\).*/\1/p')
  P1=$(echo "$LINE" | sed -n 's/.* p1=\([0-9]*\).*/\1/p'); P10=$(echo "$LINE" | sed -n 's/.* p10=\([0-9]*\).*/\1/p'); MED=$(echo "$LINE" | sed -n 's/.* median=\([0-9]*\).*/\1/p')
  MU=$(echo "$LINE" | sed -n 's/.* mu=\([0-9.]*\).*/\1/p')
  printf "%s\t%s\tN=%s\tmu=%s\tfix=%s\tmin=%s\tp1=%s\tp10=%s\tmedian=%s\n" "$N" "$SPEC" "$N" "$MU" "$FIX" "$MIN" "$P1" "$P10" "$MED" >> "$OUT"
done < "$LIST"
echo DONE >> "$OUT"
