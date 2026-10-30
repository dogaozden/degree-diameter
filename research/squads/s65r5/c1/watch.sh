#!/bin/bash
# time-box guard: stop the sweep loop right after chunk 51-100 (chunk 3 would overrun the 35-min box)
cd /home/user/degree-diameter/research/squads/s65r5/c1
until grep -q "chunk lines 51-100 done" progress.txt; do sleep 2; done
kill 13712 2>/dev/null
sleep 1
pkill -f "IDS:=\[165," 2>/dev/null
sleep 2
pkill -f "IDS:=\[165," 2>/dev/null
echo "$(date -u +%T) STOPPED sweep by time box after chunk lines 51-100 (chunk 3 not run)" >> progress.txt
