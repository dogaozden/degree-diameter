#!/bin/bash
# Squad d16D10-r1, card c2: one run of ORBIT="3 5 1" haar_sym on SL(2,p) x Z_n at proxy (16,8).
# usage: run_one.sh SHAPE P N SEED      (env BUDGET = wall-clock seconds per run, default 160)
# Output: research/squads/d16D10-r1/c2/logs/<SHAPE>_sl<P>_n<N>_s<SEED>.log  (RESULT line + stderr + exit code)
set -u
T=/tmp/claude-0/-home-user-degree-diameter/4ce63409-b0f8-5c33-8f23-00173ad34031/scratchpad/tools/research/structured
C2=/home/user/degree-diameter/research/squads/d16D10-r1/c2
BUDGET=${BUDGET:-160}
shape=$1; p=$2; n=$3; seed=$4
mkdir -p "$C2/logs"
log="$C2/logs/${shape}_sl${p}_n${n}_s${seed}.log"
ORBIT="3 5 1" THREADS=1 timeout $((BUDGET + 30)) nice -n 10 \
  "$T/haar_sym" 16 8 "$BUDGET" "$seed" 8 /dev/null sl "$p" "$n" > "$log" 2>&1
echo "exit=$?" >> "$log"
