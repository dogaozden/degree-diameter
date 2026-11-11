#!/bin/bash
# screen one group: RANDORB samples of random k=3 f=0 symmetric S at (15,8). usage: screen.sh "sl 29 373"
HERE=$(cd "$(dirname "$0")/../.." && pwd); OUT=$HERE/runs/raise_d15D8_r2/screen
tag=$(echo "$1" | tr ' ' '_')
ORBIT="3 5 0" RANDORB=${SAMPLES:-300} THREADS=1 timeout 900 "$HERE/haar_sym" 15 8 1 1 8 /dev/null $1 > "$OUT/$tag.log" 2>&1
echo "$1 | $(grep -h 'RANDORB d=' "$OUT/$tag.log" | sed 's/.*fix=/fix=/' | cut -c1-140)" >> "$OUT/summary.txt"
