#!/bin/bash
# Card c8 driver: exhaustive haarex3 over hi_list_7.txt, one process at a time, 35-minute box.
W=/home/user/degree-diameter/research/squads/s65r7/c8
T=/home/user/degree-diameter/research/s65/tools
cd "$W" || exit 1
START=$(date +%s)
while read -r ID; do
  [ -z "$ID" ] && continue
  ORD=${ID%_*}; GID=${ID#*_}
  NOW=$(date +%s); EL=$((NOW-START))
  if [ $EL -ge 1800 ]; then echo "STOP before $ID at elapsed ${EL}s" >> run.out; break; fi
  TO=$((2100-EL)); [ $TO -gt 600 ] && TO=600
  echo "START $ID elapsed=${EL}s timeout=${TO}s $(date -u +%H:%M:%S)" >> run.out
  EXP=$(gap -q -c "K:=SmallGroup($ORD,$GID);; FN:=\"hx_${ORD}_${GID}.txt\";;" $T/haarex2.g 2>&1 | grep EXPORTED | head -1)
  STRUCT=$(echo "$EXP" | sed -e 's/.*gens=[0-9]* //')
  [ -z "$STRUCT" ] && STRUCT="(export failed)"
  if [ ! -s "hx_${ORD}_${GID}.txt" ]; then
    echo "$ID | $STRUCT | 0 | - | export failed" >> table.txt; rm -f "hx_${ORD}_${GID}.txt"; continue
  fi
  timeout $TO nice -n 10 $T/haarex3 "hx_${ORD}_${GID}.txt" > "h${ORD}_${GID}.log" 2>&1
  RC=$?
  rm -f "hx_${ORD}_${GID}.txt"
  NV=$(grep -c '^VALID' "h${ORD}_${GID}.log")
  if [ $NV -gt 0 ]; then
    grep '^VALID' "h${ORD}_${GID}.log" > "VALID_${ORD}_${GID}.txt"
    echo "RECORD CANDIDATE $ID: $(cat VALID_${ORD}_${GID}.txt | tr '\n' ' ')" >> RECORD_CANDIDATES.txt
  fi
  DONEL=$(grep '^DONE' "h${ORD}_${GID}.log")
  LASTP=$(grep '^PAIR' "h${ORD}_${GID}.log" | tail -1)
  SUMA=$(grep '^PAIR' "h${ORD}_${GID}.log" | sed -e 's/.*acovers=//' | awk '{s+=$1} END {print s+0}')
  if [ -n "$DONEL" ]; then
    P=$(echo "$DONEL" | sed -e 's/.*pairs=0\.\.\([0-9]*\).*/\1/')
    A=$(echo "$DONEL" | sed -e 's/.*Acovered=\([0-9]*\).*/\1/')
    V=$(echo "$DONEL" | sed -e 's/.*valid=\([0-9]*\).*/\1/')
    COV="0..$P (DONE)"
    LINE="$ID | $STRUCT | $COV | $A | $V valid, minA=$(echo "$DONEL" | sed -e 's/.*minA=//')"
  else
    I=$(echo "$LASTP" | awk '{print $2}')
    COV="partial: last PAIR ${I:-none} (timeout ${TO}s, rc=$RC)"
    LINE="$ID | $STRUCT | $COV | sum-PAIR $SUMA | $NV valid so far"
  fi
  echo "$LINE" >> table.txt
  echo "DONE_LINE $ID: $LINE" >> run.out
  echo "END $ID rc=$RC $(date -u +%H:%M:%S)" >> run.out
done < /home/user/degree-diameter/research/s65/haar/hi_list_7.txt
echo "ALL_FINISHED $(date -u +%H:%M:%S)" >> run.out
