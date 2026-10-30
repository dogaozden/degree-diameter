#!/bin/bash
# c4: exhaustive haarex3 over research/s65/haar/hi_list_3.txt, one process at a time, stop starting groups at 10:50 UTC.
cd /home/user/degree-diameter/research/squads/s65r7/c4
TOOLS=/home/user/degree-diameter/research/s65/tools
END=$(date -u -d "2026-10-30 10:50:00" +%s)
for ID in $(cat /home/user/degree-diameter/research/s65/haar/hi_list_3.txt); do
  if [ "$(date -u +%s)" -ge "$END" ]; then echo "STOPPED_BEFORE $ID (time box)" >> run_status.txt; break; fi
  ORD=${ID%_*}; GID=${ID#*_}
  echo "START $ID $(date -u +%T)" >> run_status.txt
  gap -q -c "K:=SmallGroup($ORD,$GID);; FN:=\"hx_${ID}.txt\";;" $TOOLS/haarex2.g < /dev/null > exp_${ID}.out 2>&1
  STRUCT=$(grep EXPORTED exp_${ID}.out | sed -E 's/.*gens=[0-9]+ //')
  [ -z "$STRUCT" ] && STRUCT="EXPORT_FAILED"
  timeout 600 nice -n 10 $TOOLS/haarex3 hx_${ID}.txt > h${ID}.log 2>&1 < /dev/null
  RC=$?
  rm -f hx_${ID}.txt
  if grep -q '^DONE' h${ID}.log; then
    DONE=$(grep '^DONE' h${ID}.log)
    P=$(echo "$DONE" | sed -E 's/.*pairs=[0-9]+\.\.([0-9]+).*/\1/')
    A=$(echo "$DONE" | sed -E 's/.*Acovered=([0-9]+).*/\1/')
    V=$(echo "$DONE" | sed -E 's/.*valid=([0-9]+).*/\1/')
    COV="0..$P"
  else
    I=$(grep '^PAIR' h${ID}.log | tail -1 | awk '{print $2}')
    A=$(grep -c 'acovers=[1-9]' h${ID}.log)
    V=$(grep -c '^VALID' h${ID}.log)
    COV="0..${I:-none}(TIMEOUT rc=$RC)"
  fi
  echo "$ID | $STRUCT | $COV | $A | $V" >> table.txt
  if grep -q '^VALID' h${ID}.log; then
    echo "!!! RECORD CANDIDATE $ID:" >> run_status.txt
    grep '^VALID' h${ID}.log >> run_status.txt
    grep '^VALID' h${ID}.log > VALID_${ID}.txt
  fi
  echo "END $ID $(date -u +%T) rc=$RC $DONE" >> run_status.txt
done
echo "ALL_DONE $(date -u +%T)" >> run_status.txt
