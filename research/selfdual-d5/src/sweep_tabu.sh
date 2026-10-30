#!/bin/bash
# sweep_tabu.sh LIST [P]: run_tabu.sh on every "N ID ..." line of LIST, P in parallel.
cd "$(dirname "$0")/.."
awk '{print $1, $2}' "$1" | xargs -P ${2:-1} -n 2 src/run_tabu.sh
echo "SWEEP DONE $1 $(date -u +%H:%M)" >> logs/K${K:-9}/tabu.txt
