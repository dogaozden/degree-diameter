#!/bin/bash
# RANDORB tail check on all 46 candidates: one haar_sym process at a time, timeout 120, nice 19, 1000 samples, seed 1, K 8.
HERE=/home/user/degree-diameter/research/squads/d10D8-r2/c1
RAW=$HERE/randorb_all_raw.txt
: > "$RAW"
cd /home/user/degree-diameter/research/structured || exit 1
while IFS=$'\t' read -r N N2 MU NN SPEC; do
  case "$N" in '#'*|'') continue ;; esac
  echo "## N=$N spec=[$SPEC]" >> "$RAW"
  ORBIT="3 3 1" RANDORB=1000 timeout 120 nice -n 19 ./haar_sym 10 8 1 1 8 /dev/null $SPEC < /dev/null 2>&1 | grep -E "^RANDORB d=" >> "$RAW"
  echo "## rc=${PIPESTATUS[0]}" >> "$RAW"
done < "$HERE/candidates.tsv"
echo "## driver CPU (bash times, user sys):" >> "$RAW"
times >> "$RAW"
