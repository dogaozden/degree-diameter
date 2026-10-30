#!/bin/bash
# card c7: exhaustive haarex3 over r8_list_6, one process at a time, stop starting groups after DEADLINE
cd /home/user/degree-diameter/research/squads/s65r8/c7
LIST=/home/user/degree-diameter/research/s65/haar/r8_list_6.txt
DEADLINE=$(( $(date +%s) + 30*60 ))
: > table.txt
while read ID_LINE; do
  [ -z "$ID_LINE" ] && continue
  ORDER=${ID_LINE%_*}; ID=${ID_LINE#*_}
  if [ $(date +%s) -ge $DEADLINE ]; then echo "SKIP $ID_LINE (deadline)" >> run_status.txt; continue; fi
  echo "START $ID_LINE $(date +%T)" >> run_status.txt
  STRUCT=$(gap -q -c "K:=SmallGroup($ORDER,$ID);; FN:=\"hx_${ORDER}_${ID}.txt\";;" /home/user/degree-diameter/research/s65/tools/haarex2.g 2>&1 | grep EXPORTED | tail -1)
  if [ ! -s hx_${ORDER}_${ID}.txt ]; then echo "$ID_LINE | export failed | - | - | -" >> table.txt; continue; fi
  timeout 600 nice -n 10 /home/user/degree-diameter/research/s65/tools/haarex3 hx_${ORDER}_${ID}.txt > h${ORDER}_${ID}.log 2>&1
  RC=$?
  rm -f hx_${ORDER}_${ID}.txt
  DONE=$(grep '^DONE' h${ORDER}_${ID}.log | tail -1)
  LASTPAIR=$(grep '^PAIR' h${ORDER}_${ID}.log | tail -1)
  ASIDE=$(grep -c '^ASIDE' h${ORDER}_${ID}.log)
  VALIDL=$(grep '^VALID' h${ORDER}_${ID}.log | head -3)
  if [ -n "$VALIDL" ]; then VALID="YES: $VALIDL"; else VALID="no"; fi
  if [ -n "$DONE" ]; then PAIRS=$(echo "$DONE" | sed -n 's/.*pairs=\(0\.\.[0-9]*\).*/\1/p'); ACOV=$(echo "$DONE" | sed -n 's/.*Acovered=\([0-9-]*\).*/\1/p'); STATUS="done"
  else PAIRS="0..$(echo "$LASTPAIR" | awk '{print $2}') (TIMEOUT rc=$RC)"; ACOV="?"; STATUS="partial"; fi
  echo "$ID_LINE | $STRUCT | $PAIRS | Acovered=$ACOV aside_lines=$ASIDE | valid: $VALID" >> table.txt
  echo "END $ID_LINE rc=$RC $STATUS $(date +%T) $DONE" >> run_status.txt
done < $LIST
echo "ALLDONE $(date +%T)" >> run_status.txt
