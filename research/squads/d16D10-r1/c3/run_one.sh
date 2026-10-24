#!/bin/bash
# card c3 (squad d16D10-r1): one haar_sym run. args: TAG SEED SECS GROUP... N
# Writes logs/TAG.out (RESULT line), logs/TAG.err (progress, mu), logs/TAG.rc (exit code, wall seconds).
T=/tmp/claude-0/-home-user-degree-diameter/4ce63409-b0f8-5c33-8f23-00173ad34031/scratchpad/tools/research/structured
DIR=/home/user/degree-diameter/research/squads/d16D10-r1/c3/logs
tag=$1; seed=$2; secs=$3; shift 3
s=$(date +%s.%N)
ORBIT="3 5 1" THREADS=1 timeout $((secs + 60)) nice -n 10 "$T/haar_sym" 16 8 "$secs" "$seed" 8 /dev/null "$@" > "$DIR/$tag.out" 2> "$DIR/$tag.err"
rc=$?
e=$(date +%s.%N)
echo "rc=$rc wall=$(python3 -c "print(round($e-$s,1))")" > "$DIR/$tag.rc"
