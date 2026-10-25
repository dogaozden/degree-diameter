#!/bin/bash
# c1: stop the (3,10) b33_0 lift screen at the deadline, then re-anneal the three lowest-cost groups (60 s each, seeds 2-4).
export OUTDIR=/home/user/degree-diameter/research/squads/r2-smallfam/c1
export SCRATCH=/home/user/degree-diameter/research/squads/r2-smallfam/c1/tmp
LOG=$OUTDIR/pipeline.log
DEADLINE=$(date -u -d "2026-10-25 04:59:00" +%s)
while [ "$(date -u +%s)" -lt "$DEADLINE" ]; do sleep 2; done
PID=$(pgrep -f "^python3 lscreen.py bases/b33_0.txt 10 134 145" | head -n 1)
if [ -n "$PID" ]; then kill -TERM "$PID"; fi
echo "screen stopped at $(date -u +%T) (pid ${PID:-none})" >> "$LOG"
sleep 2
cd /home/user/degree-diameter/research/theorems/smallfam || exit 1
timeout 1200 nice -n 10 python3 /home/user/degree-diameter/research/squads/r2-smallfam/c1/reanneal.py 3 60 2 >> "$LOG" 2>&1
echo "reanneal finished at $(date -u +%T)" >> "$LOG"
