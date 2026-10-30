#!/bin/bash
# sweep.sh LIST [P]: run1.sh on every "N ID ..." line of LIST, P in parallel (K, MAXEV, ... from the environment).
cd "$(dirname "$0")/.."
awk '{print $1, $2}' "$1" | xargs -P ${2:-3} -n 2 src/run1.sh
echo "SWEEP DONE $1 $(date -u +%H:%M)" >> logs/K${K:-6}/sweep.txt
