#!/bin/bash
# usage: drive.sh BUDGET_SECONDS. Runs haarex3 (one process at a time, timeout 300 nice 10) over queue.txt.
# Closed groups (DONE line in logs/ORD_ID.out) are skipped; a killed run is resumed from the next pair (last PAIR+1).
cd /home/user/degree-diameter/research/squads/handsoff-65/c19 || exit 1
BUDGET=${1:-240}
start=$(date +%s)
while read ord id inv; do
  log=logs/${ord}_${id}.out
  if [ -f "$log" ] && grep -q '^DONE' "$log"; then continue; fi
  now=$(date +%s); el=$((now-start))
  if [ $el -ge $BUDGET ]; then echo "BUDGET_OUT elapsed=$el"; break; fi
  f=g/${ord}_${id}.txt
  if [ ! -f "$f" ]; then
    timeout 300 nice -n 10 gap -q -c "K:=SmallGroup($ord,$id);; FN:=\"$f\";;" haarex2.g > logs/${ord}_${id}.export 2>&1
    if [ ! -s "$f" ]; then echo "$ord $id NOEXPORT" | tee -a status_log.txt; echo "NOEXPORT" > "$log"; continue; fi
  fi
  next=0
  if [ -f "$log" ]; then
    p=$(grep '^PAIR ' "$log" | awk '{print $2}' | sort -n | tail -1)
    if [ -n "$p" ]; then next=$((p+1)); fi
  fi
  t0=$(date +%s)
  timeout 300 nice -n 10 ./haarex3 "$f" $next 1000000 >> "$log" 2>&1
  rc=$?
  t1=$(date +%s)
  if grep -q '^DONE' "$log"; then st=CLOSED; else st=PARTIAL_rc$rc; fi
  nv=$(grep -c '^VALID' "$log"); na=$(grep -c '^ASIDE' "$log")
  last=$(grep '^PAIR ' "$log" | awk '{print $2}' | sort -n | tail -1)
  echo "$ord $id inv=$inv $st from=$next lastpair=$last valid=$nv aside=$na secs=$((t1-t0)) $(grep '^DONE' "$log" | tail -1)" | tee -a status_log.txt
  if [ $nv -gt 0 ]; then echo "!!! VALID found $ord $id" | tee -a status_log.txt; break; fi
done < queue.txt
echo "DRIVE_END $(date -u +%H:%M:%S)"
