#!/bin/bash
# ZONLYDUP screen: one haar_zopt process at a time, timeout 120, nice 19. Raw output: zdup_raw.txt
HERE=/home/user/degree-diameter/research/squads/d10D8-r2/c1
RAW=$HERE/zdup_raw.txt
: > "$RAW"
cd /home/user/degree-diameter/research/d10D8/zopt || exit 1
while IFS=$'\t' read -r N N2 MU NN SPEC; do
  case "$N" in '#'*|'') continue ;; esac
  echo "## N=$N mu=$MU spec=[$SPEC]" >> "$RAW"
  ORBIT="3 3 1" ZOPT=r:3 ZONLYDUP=1 timeout 120 nice -n 19 ./haar_zopt 10 8 1 1 8 /dev/null $SPEC < /dev/null >> "$RAW" 2>&1
  echo "## rc=$?" >> "$RAW"
done < "$HERE/candidates.tsv"
echo "## driver CPU (bash times, user sys):" >> "$RAW"
times >> "$RAW"
