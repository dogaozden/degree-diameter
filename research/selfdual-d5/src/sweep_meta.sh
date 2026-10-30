#!/bin/bash
# sweep_meta.sh LIST [P]: run_meta.sh on every "N P K D" line of LIST, P in parallel.
cd "$(dirname "$0")/.."
awk '{print $1, $2, $3, $4}' "$1" | xargs -P ${2:-1} -n 4 src/run_meta.sh
echo "SWEEP DONE $1 $(date -u +%H:%M)" >> logs/K${K:-9}/meta.txt
