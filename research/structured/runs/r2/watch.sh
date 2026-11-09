#!/bin/bash
# Waits until some round-2 log reports a solution (best=0) or 1500 s pass; prints what it found.
cd /home/user/degree-diameter/research/structured/runs/r2
end=$(( $(date +%s) + 1500 ))
while [ $(date +%s) -lt $end ]; do
  hits=$(grep -l "best=0 " spool/*/*.log 2>/dev/null)
  if [ -n "$hits" ]; then echo "SOLVED: $hits"; grep -h RESULT $hits; exit 0; fi
  sleep 20
done
echo "no solution yet at $(date -u +%H:%M); running: $(pgrep -a -x haar_sym | wc -l)"
