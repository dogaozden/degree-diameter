#!/bin/bash
# c27 driver (copy of c19/drive.sh, with per-run timeouts capped so one call stays under ~290 s).
# usage: drive.sh BUDGET_SECONDS. One heavy process at a time, foreground. Closed groups (DONE in logs/) are skipped.
cd /home/user/degree-diameter/research/squads/handsoff-65/c27 || exit 1
BUDGET=${1:-200}
start=$(date +%s)
end=$((start+BUDGET))
capt() { # cap of seconds for one process: min(300, time left in budget)
  local left=$(( end - $(date +%s) )); if [ $left -gt 300 ]; then echo 300; else echo $left; fi; }
while read ord id inv; do
  log=logs/${ord}_${id}.out
  if [ -f "$log" ] && grep -q '^DONE' "$log"; then continue; fi
  c=$(capt); if [ $c -lt 15 ]; then echo "BUDGET_OUT"; break; fi
  f=g/${ord}_${id}.txt
  if [ ! -f "$f" ]; then
    timeout $c nice -n 10 gap -q -c "K:=SmallGroup($ord,$id);; FN:=\"$f\";;" haarex2.g > logs/${ord}_${id}.export 2>&1
    if [ ! -s "$f" ]; then echo "$ord $id NOEXPORT rc=$?" | tee -a status_log.txt; continue; fi
  fi
  c=$(capt); if [ $c -lt 15 ]; then echo "BUDGET_OUT"; break; fi
  next=0
  if [ -f "$log" ]; then
    p=$(grep '^PAIR ' "$log" | awk '{print $2}' | sort -n | tail -1)
    if [ -n "$p" ]; then next=$((p+1)); fi
  fi
  t0=$(date +%s)

  (ulimit -v 1400000; timeout $c nice -n 10 ./haarex3 "$f" $next 1000000 >> "$log" 2>&1)
  rc=$?
  t1=$(date +%s)
  if grep -q '^DONE' "$log"; then st=CLOSED; else st=PARTIAL_rc$rc; fi
  nv=$(grep -c '^VALID' "$log"); na=$(grep -c '^ASIDE' "$log")
  last=$(grep '^PAIR ' "$log" | awk '{print $2}' | sort -n | tail -1)
  echo "$ord $id inv=$inv $st from=$next lastpair=$last valid=$nv aside=$na secs=$((t1-t0)) $(grep '^DONE' "$log" | tail -1 | cut -c1-60)" | tee -a status_log.txt
  if [ $nv -gt 0 ]; then echo "!!! VALID found $ord $id" | tee -a status_log.txt; break; fi
done < queue.txt
echo "DRIVE_END $(date -u +%H:%M:%S)"
