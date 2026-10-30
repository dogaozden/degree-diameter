#!/bin/bash
# runs each group in todo.txt sequentially: export, haarex2, delete export. DEADLINE (epoch) = no new group after it.
C=/home/user/degree-diameter/research/squads/s65r5/c7
T=/home/user/degree-diameter/research/s65/tools
cd "$C" || exit 1
ENDRUN=$(date -d "09:50" +%s)
while read id start NP; do
  case "$id" in \#*|"") continue;; esac
  now=$(date +%s); rem=$((ENDRUN - now))
  if [ "$rem" -lt 120 ]; then echo "SKIP $id (deadline)" >> driver.log; continue; fi
  o=${id%_*}; i=${id#*_}
  echo "START $id start=$start at $(date +%T) rem=$rem" >> driver.log
  gap -q -c "K:=SmallGroup($o,$i);; FN:=\"hx_${o}_${i}.txt\";;" "$T/haarex2.g" > "exp_${o}_${i}.out" 2>&1
  if [ ! -s "hx_${o}_${i}.txt" ]; then echo "EXPORT FAILED $id" >> driver.log; continue; fi
  head -1 "exp_${o}_${i}.out" >> driver.log
  if [ "$start" -eq 0 ]; then
    timeout "$rem" nice -n 10 "$T/haarex2" "hx_${o}_${i}.txt" > "h${o}_${i}.log" 2>&1
    echo "RC $? $id" >> driver.log
  else
    timeout "$rem" nice -n 10 "$T/haarex2" "hx_${o}_${i}.txt" "$start" "$NP" > "h${o}_${i}_resume.log" 2>&1
    echo "RC $? $id resume from $start NP=$NP" >> driver.log
  fi
  rm -f "hx_${o}_${i}.txt"
  echo "END $id at $(date +%T)" >> driver.log
done < todo.txt
echo "ALLDONE $(date +%T)" >> driver.log
