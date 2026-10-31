#!/bin/bash
# sweep_fmeta.sh LIST [P]: run_fmeta.sh on every "N M K R ..." line of LIST, P in parallel (env K = valency).
cd "$(dirname "$0")/.."
awk '{print $1, $2, $3, $4}' "$1" | xargs -P ${2:-1} -n 4 src/run_fmeta.sh
echo "SWEEP DONE $1 $(date -u +%H:%M)" >> ${LOGDIR:-logs/K${K:-10}}/fmeta.txt
