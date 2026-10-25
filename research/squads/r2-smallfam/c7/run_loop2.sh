#!/bin/bash
# c7: the fifteen 5+5 bases over orders 17-25 with fastscreen.py (lscreen with cached tables), one base after another.
# No new base starts after $DEADLINE (epoch seconds). Groups already in the TSV are skipped (lscreen resumes).
export OUTDIR=/home/user/degree-diameter/research/squads/r2-smallfam/c7
export SCRATCH=/home/user/degree-diameter/research/squads/r2-smallfam/c7/tmp
export THREADS=1
cd /home/user/degree-diameter/research/theorems/smallfam || exit 1
LOG=$OUTDIR/loop.log
for i in $(seq 0 14); do
  if [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "no new base after $(date -u +%H:%M:%S)" >> "$LOG"; break; fi
  echo "=== b55_$i fast start $(date -u +%H:%M:%S)" >> "$LOG"
  timeout 1200 nice -n 10 python3 /home/user/degree-diameter/research/squads/r2-smallfam/c7/fastscreen.py bases/b55_$i.txt 7 17 25 --secs 3 --abmin 1 --abmax 1000000 >> "$LOG" 2>&1
  echo "=== b55_$i end $(date -u +%H:%M:%S) rc=$?" >> "$LOG"
done
echo "LOOP-FINISHED $(date -u +%H:%M:%S)" >> "$LOG"
