#!/bin/bash
# One haar_sym job for the raise-d15D8 cell: ORBIT k=3 m=5 f=0, single thread, deterministic outfile.
# usage: raise_run.sh SECS SEED TAG GROUP...   (GROUP as haar_sym takes it, the last word is n, e.g. "sl 53 61")
HERE=$(cd "$(dirname "$0")/.." && pwd); OUT=$HERE/runs/raise_d15D8
SECS=$1; SEED=$2; TAG=$3; shift 3
[ -s "$OUT/$TAG.txt" ] && exit 0
ORBIT="3 5 0" THREADS=1 nice -n 5 timeout $((SECS + 300)) "$HERE/haar_sym" 15 8 "$SECS" "$SEED" 8 "$OUT/$TAG.sol" "$@" > "$OUT/$TAG.log" 2>&1
echo "$(date +%T) $TAG $(grep -h RESULT "$OUT/$TAG.log" | cut -c1-120)" >> "$OUT/summary.txt"
