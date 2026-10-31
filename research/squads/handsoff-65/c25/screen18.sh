#!/bin/bash
# usage: screen18.sh SECS SEED DEADLINE_EPOCH TABLE...   (c25) runs t18 "1,6|1,6" N=5,1,1,0 on each table
# that has order-6 elements; appends "table<TAB>order<TAB>n<TAB>best<TAB>tbest<TAB>secs" to scan/screen.tsv
D=/home/user/degree-diameter/research/squads/handsoff-65/c25
S=$1; SD=$2; DL=$3; shift 3
OUT=$D/scan/screen.tsv; touch "$OUT"
for f in "$@"; do
  b=$(basename "$f" .txt)
  [ "$(date +%s)" -ge "$DL" ] && exit 0
  grep -q "^$b	" "$OUT" 2>/dev/null && continue
  m=$(head -1 "$f")
  o6=$(python3 $D/has6.py "$f" | awk '{print $3}')
  [ "$o6" = "ord6=0" ] && continue
  LOG=$D/scan/$b.s$SD.log
  E=$D/scan/$b.s$SD.edges
  TLIM=$S timeout $((S+60)) nice -n 10 $D/t18 "$f" 6 5,1,1,0 $SD 100000000 12 "$E" > "$LOG" 2>&1
  best=$(grep "^RESULT" "$LOG" | awk '{print $3}'); [ -z "$best" ] && best=ERR
  tb=$(grep "^best $best " "$LOG" | tail -1 | awk '{print $5}')
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$m" "$(( m*7/3 ))" "$best" "${tb:-?}" "$S" >> "$OUT"
  if [ "$best" != "ERR" ] && [ "$best" -gt 6 ] 2>/dev/null; then rm -f "$E" "$E.par"; fi
done
