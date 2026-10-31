#!/bin/bash
# usage: screen23.sh K NSPLIT SECS SEED DEADLINE_EPOCH FILE.txt...
# Runs t18 (hub type "1,K|1,K", split NSPLIT) on each group table; skips abelian groups and groups already in the tsv.
# Appends "group<TAB>name<TAB>K<TAB>N<TAB>best<TAB>sec" to scan/t<K>_<N>.tsv. Edge files kept only for best < 60.
K=$1; NS=$2; S=$3; SD=$4; DL=$5; shift 5
D=/home/user/degree-diameter/research/squads/handsoff-65/c23
TAG=t${K}_$(echo "$NS" | tr ',' '-')
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
  E=$D/scan/$TAG.$b.best.edges
  t0=$(date +%s)
  timeout $((S*3+30)) env TLIM=$S nice -n 10 $D/t18 "$f" $K $NS $SD 100000 12 "$E" > "$LOG" 2>&1
  best=$(grep "^RESULT" "$LOG" | awk '{print $3}')
  [ -z "$best" ] && best=ERR
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$(head -c 30 "$nm" | tr -d '\t')" "$K" "$NS" "$best" "$(( $(date +%s) - t0 ))" >> "$OUT"
  [ "$best" = "0" ] && echo "HIT $b $K" >> "$OUT"
  if [ "$best" != "0" ] && [ -f "$E" ] && { [ "$best" = ERR ] || [ "$best" -gt 60 ]; }; then rm -f "$E"; fi
  rm -f "$LOG"
done
