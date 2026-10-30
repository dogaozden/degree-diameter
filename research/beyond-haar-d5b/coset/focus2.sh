#!/bin/bash
# (7,5) near misses, long anneals with the fixed drivers (SECS is CPU time; wall-clock safety timeout 8x + 600 s)
cd "$(dirname "$0")"
rm -rf tmp_1206_2_19862 tmp_1210_2_7823
./sweep.sh 1206 2 7 120 "[1]" 3
./sweep.sh 1815 3 7 120 "[3]" 3
./sweep.sh 1210 2 7 120 "[13, 12, 15]" 2
echo "focus2 done $(date -u +%H:%M)" >> logs/queue75.log
