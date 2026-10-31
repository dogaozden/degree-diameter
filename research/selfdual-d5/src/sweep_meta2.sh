#!/bin/bash
# sweep_meta2.sh LIST [P]: run_meta2.sh on every "N P K D" line of LIST, P in parallel.
cd "$(dirname "$0")/.."
awk '{print $1, $2, $3, $4}' "$1" | xargs -P ${2:-1} -n 4 src/run_meta2.sh
echo "SWEEP DONE $1 $(date -u +%H:%M)" >> logs/K${K:-9}/meta2.txt
