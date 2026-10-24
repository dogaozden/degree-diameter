#!/bin/bash
# RANDORB tail check: one haar_sym process at a time, timeout 120, nice 19, 3000 random symmetric S (seed 1, K 8).
HERE=/home/user/degree-diameter/research/squads/d10D8-r2/c1
RAW=$HERE/randorb_raw.txt
: > "$RAW"
cd /home/user/degree-diameter/research/structured || exit 1
for SPEC in "pgl 27 31" "sl 32 19" "sl 27 31" "pgl 32 19" "psl 23 97"; do
  echo "## spec=[$SPEC]" >> "$RAW"
  ORBIT="3 3 1" RANDORB=3000 timeout 120 nice -n 19 ./haar_sym 10 8 1 1 8 /dev/null $SPEC < /dev/null 2>&1 | grep -E "^RANDORB d=|^RANDORB cost0" >> "$RAW"
  echo "## rc=${PIPESTATUS[0]}" >> "$RAW"
done
echo "## driver CPU (bash times, user sys):" >> "$RAW"
times >> "$RAW"
