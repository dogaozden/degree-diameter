#!/bin/bash
# usage: screen22.sh K NSPLIT SECS SEED DEADLINE_EPOCH TABLE.txt...
# t18 tabu (type "1,K|1,K") on each nonabelian group table; appends group<TAB>name<TAB>K<TAB>N<TAB>best<TAB>sec to scan/<TAG>.tsv
# Keeps edge files only when best is small (<= 20). Skips groups already in the tsv.
K=$1; NS=$2; S=$3; SD=$4; DL=$5; shift 5
D=/home/user/degree-diameter/research/squads/handsoff-65/c22
TAG=k${K}_$(echo "$NS" | tr ',' '-')
OUT=$D/scan/$TAG.tsv
touch "$OUT"
for f in "$@"; do
  b=$(basename "$f" .txt)
  nm=$D/groups/$b.name
  [ -f "$nm" ] || continue
  grep -q "abelian=true" "$nm" && continue
  [ "$(date +%s)" -ge "$DL" ] && exit 0
  grep -q "^$b	" "$OUT" 2>/dev/null && continue
  LOG=$D/scan/$TAG.$b.log
  E=$D/scan/$TAG.$b.edges
  t0=$(date +%s)
  TLIM=$S timeout $((S+60)) nice -n 10 $D/t18 "$f" $K $NS $SD 100000000 12 "$E" > "$LOG" 2>&1
  best=$(grep "^RESULT" "$LOG" | awk '{print $3}')
  [ -z "$best" ] && best=ERR
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$(head -c 30 "$nm" | tr -d '\t')" "$K" "$NS" "$best" "$(( $(date +%s) - t0 ))" >> "$OUT"
  [ "$best" = "0" ] && echo "HIT $b $K $NS" >> "$OUT"
  if [ "$best" != "0" ] && [ -f "$E" ]; then [ "$best" -gt 20 ] 2>/dev/null && rm -f "$E"; fi
done
