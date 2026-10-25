#!/bin/bash
# c7: lscreen of the fifteen 5+5 bases over orders 17-25, one base after another (THREADS=1).
# Stops starting new bases after the deadline (epoch seconds in $DEADLINE).
export OUTDIR=/home/user/degree-diameter/research/squads/r2-smallfam/c7
export SCRATCH=/home/user/degree-diameter/research/squads/r2-smallfam/c7/tmp
export THREADS=1
mkdir -p "$SCRATCH"
cd /home/user/degree-diameter/research/theorems/smallfam || exit 1
LOG=$OUTDIR/loop.log
for i in $(seq 0 14); do
  if [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "deadline reached before b55_$i $(date -u +%H:%M:%S)" >> "$LOG"; break; fi
  echo "=== b55_$i start $(date -u +%H:%M:%S)" >> "$LOG"
  timeout 1200 nice -n 10 python3 lscreen.py bases/b55_$i.txt 7 17 25 --secs 3 --abmin 1 --abmax 1000000 >> "$LOG" 2>&1
  echo "=== b55_$i end $(date -u +%H:%M:%S) rc=$?" >> "$LOG"
done
echo "LOOP-FINISHED $(date -u +%H:%M:%S)" >> "$LOG"
