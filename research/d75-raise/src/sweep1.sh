#!/bin/bash
# sweep1.sh LIST [P]: run1.sh on every "N ID ..." line of LIST, P in parallel.
cd "$(dirname "$0")/.."
awk '{print $1, $2}' "$1" | xargs -P ${2:-3} -n 2 src/run1.sh
echo "SWEEP DONE $1" >> logs/sweep.txt
