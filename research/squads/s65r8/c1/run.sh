#!/bin/bash
# card c1 driver: sequential exhaustive haarex3 over r8_list_0.txt, one process at a time
D=/home/user/degree-diameter/research/squads/s65r8/c1
T=/home/user/degree-diameter/research/s65/tools
START=$(date +%s)
cd "$D"
for id in $(cat /home/user/degree-diameter/research/s65/haar/r8_list_0.txt); do
  ORDER=${id%_*}; ID=${id#*_}
  el=$(( $(date +%s) - START ))
  if [ $el -gt 1800 ]; then
    echo "$id | NOT REACHED (time box) | - | - | -" >> table.txt
    continue
  fi
  if [ -f h${id}.log ] && grep -q DONE h${id}.log; then continue; fi
  gap -q -c "K:=SmallGroup($ORDER,$ID);; FN:=\"hx_${id}.txt\";;" $T/haarex2.g > gap_${id}.out 2>&1
  struct=$(grep EXPORTED gap_${id}.out | sed 's/^EXPORTED [^ ]* //')
  if [ ! -s hx_${id}.txt ]; then
    echo "$id | EXPORT FAILED | - | - | - | $struct" >> table.txt; continue
  fi
  s=$(date +%s)
  timeout 600 nice -n 10 $T/haarex3 hx_${id}.txt > h${id}.log 2>&1
  rc=$?
  e=$(( $(date +%s) - s ))
  rm -f hx_${id}.txt
  if grep -q '^VALID' h${id}.log; then
    grep '^VALID' h${id}.log > VALID_${id}.txt
    echo "!!! VALID $id : see $D/VALID_${id}.txt" >> alerts.txt
  fi
  done_line=$(grep '^DONE' h${id}.log)
  if [ -n "$done_line" ]; then
    pairs=$(echo "$done_line" | sed -n 's/.*pairs=\([0-9.]*\).*/\1/p')
    acov=$(echo "$done_line" | sed -n 's/.*Acovered=\([-0-9]*\).*/\1/p')
    valid=$(echo "$done_line" | sed -n 's/.*valid=\([-0-9]*\).*/\1/p')
    minA=$(echo "$done_line" | sed -n 's/.*minA=\([-0-9]*\).*/\1/p')
    res="DONE"
  else
    last=$(grep '^PAIR' h${id}.log | tail -1)
    pairs="partial(rc=$rc,${e}s): $last"; acov="?"; valid="?"; minA="?"; res="TIMEOUT/PARTIAL"
  fi
  aside=$(grep -c '^ASIDE' h${id}.log)
  echo "$id | $struct | pairs ${pairs} | Acovered=${acov} | valid=${valid} minA=${minA} | $res, ${e}s, aside=$aside" >> table.txt
done
echo "ALL DONE $(date +%T)" >> table.txt
