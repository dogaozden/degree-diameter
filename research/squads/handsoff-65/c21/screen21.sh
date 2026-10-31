#!/bin/bash
# usage: screen21.sh TLIM SEED DEADLINE_EPOCH FILE.txt...   (c21: t18 on each group table, 1,6|1,6, N=5,1,1,0)
# appends "group<TAB>nsub<TAB>best<TAB>sec" to scan/screen.tsv; keeps edges only when best <= 3
D=/home/user/degree-diameter/research/squads/handsoff-65/c21
TL=$1; SD=$2; DL=$3; shift 3
OUT=$D/scan/screen.tsv; touch "$OUT"
for f in "$@"; do
  b=$(basename "$f" .txt)
  [ "$(date +%s)" -ge "$DL" ] && exit 0
  grep -q "^$b	" "$OUT" 2>/dev/null && continue
  E=$D/scan/$b.s$SD.edges; LOG=$D/scan/$b.s$SD.log
  t0=$(date +%s)
  timeout 200 nice -n 10 env TLIM=$TL SAMPLE=60 SUBS=20 $D/t18 "$f" 6 5,1,1,0 $SD 100000000 10 "$E" > "$LOG" 2>&1
  ns=$(grep -o "nsub [0-9]*" "$LOG" | awk '{print $2}')
  best=$(grep "^RESULT" "$LOG" | awk '{print $3}')
  [ -z "$best" ] && best=ERR; [ -z "$ns" ] && ns=0
  printf '%s\t%s\t%s\t%s\n' "$b" "$ns" "$best" "$(( $(date +%s) - t0 ))" >> "$OUT"
  if [ "$best" != "ERR" ] && [ "$best" -gt 3 ] 2>/dev/null; then rm -f "$E"; fi
  [ "$best" = "0" ] && echo "HIT $b" >> "$OUT"
  rm -f "$LOG"
done
