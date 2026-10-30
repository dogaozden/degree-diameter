#!/bin/bash
# card c4 driver: export + haarex2 run per group, one at a time. Hard end 09:14:30 UTC.
C4=/home/user/degree-diameter/research/squads/s65r4/c4
T=/home/user/degree-diameter/research/s65/tools
END=$(date -d "2026-10-30 09:14:30 UTC" +%s)
LAUNCH_END=$(date -d "2026-10-30 09:12:30 UTC" +%s)
cd $C4
while read id; do
  now=$(date +%s)
  if [ $now -ge $LAUNCH_END ]; then echo "SKIP $id (time)" >> driver.out; continue; fi
  o=${id%_*}; i=${id#*_}
  gap -q -c "K:=SmallGroup($o,$i);; FN:=\"hx_${o}_${i}.txt\";;" $T/haarex2.g > exp_${o}_${i}.log 2>&1
  now=$(date +%s); TO=$((END-now)); [ $TO -gt 900 ] && TO=900
  start=$(date +%s)
  timeout $TO nice -n 10 $T/haarex2 hx_${o}_${i}.txt > h${o}_${i}.log 2>&1
  rc=$?
  el=$(( $(date +%s) - start ))
  rm -f hx_${o}_${i}.txt
  echo "$id rc=$rc secs=$el $(grep -c PAIR h${o}_${i}.log) PAIR-lines $(grep '^DONE' h${o}_${i}.log)" >> driver.out
done < order.txt
echo ALLDONE >> driver.out
