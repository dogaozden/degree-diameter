#!/bin/bash
# card c3 of round s65r7: sequential exhaustive haarex3 over hi_list_2.txt (one process at a time)
cd /home/user/degree-diameter/research/squads/s65r7/c3
TOOLS=/home/user/degree-diameter/research/s65/tools
LIST=/home/user/degree-diameter/research/s65/haar/hi_list_2.txt
START_NEW_UNTIL=$(date -d "10:50:00" +%s)
HARD_END=$(date -d "10:55:00" +%s)
TABLE=table.txt
while read ID; do
  [ -z "$ID" ] && continue
  if grep -q "^$ID |" $TABLE 2>/dev/null; then continue; fi
  now=$(date +%s)
  if [ "$now" -ge "$START_NEW_UNTIL" ]; then echo "STOP before $ID (deadline 10:50)" >> driver.log; break; fi
  ORD=${ID%_*}; GID=${ID#*_}
  FN=hx_${ORD}_${GID}.txt
  EXP=$(timeout 300 gap -q -c "K:=SmallGroup($ORD,$GID);; FN:=\"$FN\";;" $TOOLS/haarex2.g 2>&1 | grep EXPORTED)
  STRUCT=$(echo "$EXP" | sed -E 's/.*gens=[0-9]+ //')
  [ -z "$STRUCT" ] && STRUCT="EXPORT FAILED"
  LOG=h${ORD}_${GID}.log
  left=$(( HARD_END - $(date +%s) )); [ $left -gt 600 ] && left=600
  echo "$(date +%T) START $ID $STRUCT timeout=$left" >> driver.log
  timeout $left nice -n 10 $TOOLS/haarex3 $FN > $LOG 2>&1
  rc=$?
  DONE=$(grep '^DONE' $LOG)
  if [ -n "$DONE" ]; then
    P=$(echo "$DONE" | sed -E 's/.*pairs=([0-9.]+) .*/\1/')
    A=$(echo "$DONE" | sed -E 's/.*Acovered=([0-9]+).*/\1/')
    V=$(echo "$DONE" | sed -E 's/.*valid=([0-9]+).*/\1/')
    MINA=$(echo "$DONE" | sed -E 's/.*minA=(-?[0-9]+).*/\1/')
    STATUS="$P"
  else
    LAST=$(grep '^PAIR' $LOG | tail -1 | awk '{print $2}')
    A=$(grep '^PAIR' $LOG | sed -E 's/.*acovers=([0-9]+).*/\1/' | awk '{s+=$1} END {print s+0}')
    V=$(grep -c '^VALID' $LOG)
    MINA=NA
    STATUS="0..${LAST:-none} (TIMEOUT rc=$rc, not finished)"
  fi
  echo "$ID | $STRUCT | $STATUS | $A | $V" >> $TABLE
  if grep -q '^VALID' $LOG; then
    grep '^VALID' $LOG > valid_${ORD}_${GID}.txt
    echo "!!! RECORD CANDIDATE $ID: $(cat valid_${ORD}_${GID}.txt | tr '\n' ' ')" >> driver.log
  fi
  echo "$(date +%T) END $ID rc=$rc $STATUS A=$A valid=$V minA=$MINA" >> driver.log
  rm -f $FN
done < $LIST
echo "$(date +%T) DRIVER EXIT" >> driver.log
