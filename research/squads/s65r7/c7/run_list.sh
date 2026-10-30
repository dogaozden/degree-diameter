#!/bin/bash
# c7: exhaustive haarex3 over hi_list_6.txt, one process at a time; stop starting groups after DEADLINE (UTC epoch).
C7=/home/user/degree-diameter/research/squads/s65r7/c7
TOOLS=/home/user/degree-diameter/research/s65/tools
LIST=/home/user/degree-diameter/research/s65/haar/hi_list_6.txt
DEADLINE=$(date -d "2026-10-30 10:50:00 UTC" +%s)
cd "$C7" || exit 1
while read -r ID; do
  [ -z "$ID" ] && continue
  if [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "STOP before $ID (deadline)"; break; fi
  ORD=${ID%_*}; GID=${ID#*_}
  if [ -s "h${ORD}_${GID}.log" ] && grep -q '^DONE' "h${ORD}_${GID}.log"; then echo "skip $ID (already done)"; continue; fi
  gap -q -c "K:=SmallGroup($ORD,$GID);; FN:=\"hx_${ORD}_${GID}.txt\";;" $TOOLS/haarex2.g > "gap_${ORD}_${GID}.out" 2>&1
  STRUCT=$(grep '^EXPORTED' "gap_${ORD}_${GID}.out" | sed 's/.*gens=[0-9]* //')
  T0=$(date +%s)
  timeout 600 nice -n 10 $TOOLS/haarex3 "hx_${ORD}_${GID}.txt" > "h${ORD}_${GID}.log" 2>&1
  RC=$?
  EL=$(( $(date +%s) - T0 ))
  DONEL=$(grep '^DONE' "h${ORD}_${GID}.log")
  LASTP=$(grep '^PAIR' "h${ORD}_${GID}.log" | tail -1 | awk '{print $2}')
  if [ -n "$DONEL" ]; then
    P=$(echo "$DONEL" | sed -E 's/.*pairs=0\.\.([0-9]+).*/\1/')
    COV="0..$P"
    ACOV=$(echo "$DONEL" | sed -E 's/.*Acovered=([0-9]+).*/\1/')
    VAL=$(echo "$DONEL" | sed -E 's/.*valid=([0-9]+).*/\1/')
  else
    COV="0..${LASTP:-none}(timeout)"
    ACOV=$(grep -c 'acovers=[1-9]' "h${ORD}_${GID}.log")
    VAL="?"
  fi
  echo "${ID} | ${STRUCT} | ${COV} | ${ACOV} | ${VAL} | ${EL}s rc=${RC}" | tee -a table.txt
  grep -H 'VALID' "h${ORD}_${GID}.log" | grep -v '^DONE' | head -5 | sed 's/^/*** RECORD CANDIDATE? /'
  rm -f "hx_${ORD}_${GID}.txt"
done < "$LIST"
echo "SCRIPT END $(date -u +%H:%M:%S)"
