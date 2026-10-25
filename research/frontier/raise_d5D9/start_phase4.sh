#!/bin/bash
# waits until phase 3 has written all 32 result lines, then runs phase 4
cd "$(dirname "$0")"
while [ "$(wc -l < phase3.log)" -lt 32 ]; do sleep 10; done
xargs -P4 -I{} ./run1.sh 300 1 8 "{}" < phase4_groups.txt > phase4.log 2>&1
