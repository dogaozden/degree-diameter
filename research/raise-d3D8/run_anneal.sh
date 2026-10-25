#!/usr/bin/env bash
# usage: run_anneal.sh BASEFILE D TAG SECS SEED SPEC... ; one lift_ex 'anneal' run, RESULT line to runs/TAG.log
cd "$(dirname "$0")"
BASE=$1; D=$2; TAG=$3; SECS=$4; SEED=$5; shift 5; SPEC="$*"
OUT=${SOLDIR:-/tmp/claude-0/-home-user-degree-diameter/b3a7a086-3c7f-55a0-951b-41dcabdee834/scratchpad/sols}
mkdir -p "$OUT"
SAFE=$(echo "$SPEC" | tr ' ' '_')
r=$(timeout $((${SECS%.*} + 60)) nice -n 5 ./lift_ex "$SPEC" "$BASE" "$D" anneal "$SECS" "$SEED" "$OUT/${TAG}_${SAFE}_s${SEED}.txt" 2>&1 | grep RESULT)
echo "$SPEC :: $r" >> runs/$TAG.log
