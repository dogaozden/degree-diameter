#!/usr/bin/env bash
# usage: run_one.sh BASEFILE D TAG SPEC... ; one lift_ex 'ex' run, RESULT line to runs/TAG.log, first solution to SOLDIR
cd "$(dirname "$0")"
BASE=$1; D=$2; TAG=$3; shift 3; SPEC="$*"
OUT=${SOLDIR:-/tmp/claude-0/-home-user-degree-diameter/b3a7a086-3c7f-55a0-951b-41dcabdee834/scratchpad/sols}
mkdir -p "$OUT"
SAFE=$(echo "$SPEC" | tr ' ' '_')
r=$(timeout 900 nice -n 5 ./lift_ex "$SPEC" "$BASE" "$D" ex "$OUT/${TAG}_${SAFE}.txt" 2>&1 | grep -E 'RESULT|SOL' | tr '\n' ' ')
echo "$SPEC :: $r" >> runs/$TAG.log
