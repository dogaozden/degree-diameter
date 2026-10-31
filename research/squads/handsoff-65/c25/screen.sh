#!/bin/bash
# usage: screen.sh TYPE NSPLIT SECS SEED DEADLINE_EPOCH FILE.txt...
# Runs shared/mcos (TYPE, N=NSPLIT) on each group table given (skips abelian ones, reads .name next to the table).
# Appends "group<TAB>name<TAB>type<TAB>N<TAB>best<TAB>sec" to scan/<TAG>.tsv. Edge files kept only for best < 60.
T=$1; NS=$2; S=$3; SD=$4; DL=$5; shift 5
D=/home/user/degree-diameter/research/squads/handsoff-65/c18
TAG=$(echo "$T-$NS" | tr '|,' '_-')
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
  timeout $((S*4+60)) env TYPE="$T" N="$NS" SECS=$S SEED=$SD EDGES="$E" nice -n 10 $D/../shared/mcos "$f" > "$LOG" 2>&1
  best=$(grep "^RESULT" "$LOG" | awk '{print $3}')
  [ -z "$best" ] && best=ERR
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$(head -c 30 "$nm" | tr -d '\t')" "$T" "$NS" "$best" "$(( $(date +%s) - t0 ))" >> "$OUT"
  [ "$best" = "0" ] && echo "HIT $b $T" >> "$OUT"
  [ "$best" != "0" ] && [ -f "$E" ] && [ "$best" -gt 60 ] 2>/dev/null && rm -f "$E"
done
