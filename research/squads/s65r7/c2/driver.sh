#!/bin/bash
# c2 driver: exhaustive haarex3 over hi_list_1.txt, one group at a time, stop starting groups after 1800 s.
cd /home/user/degree-diameter/research/squads/s65r7/c2
START=$(date +%s)
LIST=/home/user/degree-diameter/research/s65/haar/hi_list_1.txt
TOOLS=/home/user/degree-diameter/research/s65/tools
for id in $(cat $LIST); do
  NOW=$(date +%s)
  if [ $((NOW-START)) -gt 1800 ]; then echo "STOP time limit reached before $id" >> driver.log; break; fi
  ORD=${id%_*}; NUM=${id#*_}
  FN=hx_${id}.txt
  echo "START $id at $(date -u +%H:%M:%S)" >> driver.log
  gap -q -c "K:=SmallGroup($ORD,$NUM);; FN:=\"$FN\";;" $TOOLS/haarex2.g > exp_${id}.out 2>&1
  EXP=$(grep EXPORTED exp_${id}.out | head -1)
  if [ ! -s "$FN" ]; then echo "EXPORT FAILED $id" >> driver.log; echo "$id | EXPORT FAILED | - | - | -" >> table.txt; continue; fi
  T0=$(date +%s)
  timeout 600 nice -n 10 $TOOLS/haarex3 "$FN" > "h${id}.log" 2>&1
  RC=$?
  T1=$(date +%s)
  rm -f "$FN"
  STRUCT=$(echo "$EXP" | sed -E 's/.*gens=[0-9]+ //')
  [ -z "$STRUCT" ] && STRUCT="SmallGroup($ORD,$NUM)"
  DONE=$(grep '^DONE' "h${id}.log")
  NVALID=$(grep -c '^VALID' "h${id}.log")
  if [ -n "$DONE" ]; then
    PR=$(echo "$DONE" | sed -E 's/.*pairs=0\.\.([0-9]+).*/0..\1/')
    AC=$(echo "$DONE" | sed -E 's/.*Acovered=([0-9]+).*/\1/')
    V=$(echo "$DONE" | sed -E 's/.*valid=([0-9]+).*/\1/')
    STATUS="complete"
  else
    LASTP=$(grep '^PAIR' "h${id}.log" | tail -1 | awk '{print $2}')
    PR="0..${LASTP:-none}"
    AC=$(grep -c '^ASIDE\|^VALID' "h${id}.log")
    AC="$(grep -c '^PAIR' "h${id}.log") pairs done, rc=$RC TIMEOUT"
    V=$NVALID
    STATUS="TIMEOUT"
  fi
  echo "$id | $STRUCT | $PR | $AC | $V" >> table.txt
  echo "END $id rc=$RC secs=$((T1-T0)) $STATUS valid=$V nvalid_lines=$NVALID at $(date -u +%H:%M:%S)" >> driver.log
  if [ "$NVALID" -gt 0 ]; then echo "!!! VALID $id" >> driver.log; grep '^VALID' "h${id}.log" > "valid_${id}.txt"; fi
done
echo "DRIVER FINISHED at $(date -u +%H:%M:%S)" >> driver.log
