#!/bin/bash
# Card c3 driver: exhaustive haarex3 over the r8_list_2 groups, one process at a time.
cd /home/user/degree-diameter/research/squads/s65r8/c3
DEADLINE=$(( $(date +%s) + 30*60 ))
LIST=/home/user/degree-diameter/research/s65/haar/r8_list_2.txt
TOOLS=/home/user/degree-diameter/research/s65/tools
for id in $(cat $LIST); do
  ORDER=${id%_*}; GID=${id#*_}
  if [ $(date +%s) -ge $DEADLINE ]; then echo "SKIP $id deadline" >> driver.log; continue; fi
  echo "START $id $(date +%H:%M:%S)" >> driver.log
  gap -q -c "K:=SmallGroup($ORDER,$GID);; FN:=\"hx_${ORDER}_${GID}.txt\";;" $TOOLS/haarex2.g > exp_${ORDER}_${GID}.out 2>&1
  if [ ! -s hx_${ORDER}_${GID}.txt ]; then echo "EXPORT_FAILED $id" >> driver.log; continue; fi
  timeout 600 nice -n 10 $TOOLS/haarex3 hx_${ORDER}_${GID}.txt > h${ORDER}_${GID}.log 2>&1
  rc=$?
  rm -f hx_${ORDER}_${GID}.txt
  echo "END $id rc=$rc $(date +%H:%M:%S) $(grep -c PAIR h${ORDER}_${GID}.log) PAIR lines; $(grep -E '^DONE|VALID' h${ORDER}_${GID}.log | tail -2 | tr '\n' ' ')" >> driver.log
done
echo "ALLDONE $(date +%H:%M:%S)" >> driver.log
