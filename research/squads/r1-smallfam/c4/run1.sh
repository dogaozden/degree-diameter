#!/bin/bash
# usage: run1.sh NAME SECONDS SEED GROUP... n
# One haar_gen3 annealing run at (d,D)=(4,8), K=8, single thread, niced, under timeout 200.
# Writes c4/NAME_sSEED.txt (solution, only if found) and c4/NAME_sSEED.log, appends the RESULT line to c4/table.txt.
DIR=/home/user/degree-diameter/research/squads/r1-smallfam/c4
BIN=/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad/haar_gen3
NAME=$1; SECS=$2; SEED=$3; shift 3
OUT=$DIR/${NAME}_s${SEED}.txt
LOG=$DIR/${NAME}_s${SEED}.log
THREADS=1 timeout 200 nice -n 10 "$BIN" 4 8 "$SECS" "$SEED" 8 "$OUT" "$@" > "$LOG" 2>&1
RC=$?
RES=$(grep '^RESULT' "$LOG" | tail -1)
echo "$NAME seed=$SEED secs=$SECS rc=$RC :: $RES" | tee -a "$DIR/table.txt"
