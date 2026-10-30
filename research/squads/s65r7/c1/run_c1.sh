#!/bin/bash
# c1 driver (squad s65r7): sequential exhaustive haarex3 over hi_list_0.txt in order.
# No new group after 30 min from START; every run capped so that the whole driver ends by 35 min.
D=/home/user/degree-diameter/research/squads/s65r7/c1
T=/home/user/degree-diameter/research/s65/tools
L=/home/user/degree-diameter/research/s65/haar/hi_list_0.txt
cd "$D" || exit 1
START=$(date +%s); CUT=$((START+30*60)); HARD=$((START+35*60))
echo "START $(date -u +%H:%M:%S)" > driver.log
while read -r OI; do
  [ -z "$OI" ] && continue
  NOW=$(date +%s)
  if [ "$NOW" -ge "$CUT" ]; then echo "CUTOFF: not started $OI and later" >> driver.log; break; fi
  O=${OI%_*}; I=${OI#*_}
  TO=$((HARD-NOW)); [ "$TO" -gt 600 ] && TO=600
  FN="hx_${O}_${I}.txt"; LOG="h${O}_${I}.log"
  echo "== $OI start $(date -u +%H:%M:%S) timeout=$TO" >> driver.log
  gap -q -c "K:=SmallGroup($O,$I);; FN:=\"$FN\";;" $T/haarex2.g > gap_${OI}.out 2>&1
  STRUCT=$(grep '^EXPORTED' gap_${OI}.out | sed -E 's/.*gens=[0-9]+ //')
  if [ ! -s "$FN" ]; then
    echo "$OI | ${STRUCT:-gap export failed} | none | 0 | 0 (export failed)" >> table.txt
    echo "!! export failed $OI" >> driver.log; continue
  fi
  timeout "$TO" nice -n 10 $T/haarex3 "$FN" > "$LOG" 2>&1
  RC=$?
  rm -f "$FN"
  echo "end $OI rc=$RC $(date -u +%H:%M:%S)" >> driver.log
  if grep -q '^DONE' "$LOG"; then
    DL=$(grep '^DONE' "$LOG")
    P=$(echo "$DL" | sed -E 's/.*pairs=0\.\.([0-9]+).*/0..\1/')
    A=$(echo "$DL" | sed -E 's/.*Acovered=([0-9]+).*/\1/')
    V=$(echo "$DL" | sed -E 's/.*valid=([0-9]+).*/\1/')
  else
    LP=$(grep '^PAIR ' "$LOG" | tail -1 | awk '{print $2}')
    P="0..${LP:-none} PARTIAL(timeout)"
    A=$(grep '^PAIR ' "$LOG" | sed -E 's/.*acovers=([0-9]+).*/\1/' | awk '{s+=$1} END{print s+0}')
    V=$(grep -c '^VALID' "$LOG")
  fi
  echo "$OI | ${STRUCT:-?} | $P | $A | $V" >> table.txt
  if grep -q '^VALID' "$LOG"; then
    echo "!!!!! RECORD CANDIDATE $OI:" >> driver.log; grep '^VALID' "$LOG" >> driver.log
    grep '^VALID' "$LOG" > "VALID_${O}_${I}.txt"
  fi
done < "$L"
echo "ALLDONE $(date -u +%H:%M:%S)" >> driver.log
