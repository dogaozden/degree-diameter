#!/bin/bash
# card c4 driver: exhaustive haarex3 over the groups of r8_list_3.txt, one process at a time, 30-minute start deadline
cd /home/user/degree-diameter/research/squads/s65r8/c4
TOOLS=/home/user/degree-diameter/research/s65/tools
LIST=/home/user/degree-diameter/research/s65/haar/r8_list_3.txt
START=$(date +%s)
echo "start $(date -u +%H:%M:%S)" > driver.status
while read ID; do
  [ -z "$ID" ] && continue
  case "$ID" in \#*) continue;; esac
  if [ -f "h${ID}.log" ] && grep -q DONE "h${ID}.log"; then continue; fi
  NOW=$(date +%s)
  if [ $((NOW-START)) -gt 1800 ]; then echo "NOTREACHED $ID" >> driver.status; continue; fi
  ORD=${ID%_*}; GID=${ID#*_}
  EXP=$(gap -q -c "K:=SmallGroup($ORD,$GID);; FN:=\"hx_${ID}.txt\";;" $TOOLS/haarex2.g 2>&1 | grep EXPORTED)
  echo "EXPORT $ID :: $EXP" >> driver.status
  timeout 600 nice -n 10 $TOOLS/haarex3 hx_${ID}.txt > h${ID}.log 2>&1
  RC=$?
  rm -f hx_${ID}.txt
  echo "RUN $ID rc=$RC $(tail -1 h${ID}.log) $(date -u +%H:%M:%S)" >> driver.status
done < $LIST
echo "ALLDONE $(date -u +%H:%M:%S)" >> driver.status
