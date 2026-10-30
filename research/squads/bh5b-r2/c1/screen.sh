#!/bin/bash
# c1 screening pass: fast annealer, 30 s x 1 seed per (group, H, K), |H| = 2, degree 7, D = 5
cd "$(dirname "$0")"
timeout 900 nice -n 10 ./sweep.sh 1260 2 7 30 "[61,62]" 1
echo "screen 1260 done $(date -u +%H:%M:%S)" >> logs/screen.log
timeout 900 nice -n 10 ./sweep.sh 1320 2 7 30 "[133,134,135,136,137,138]" 1
echo "screen 1320 done $(date -u +%H:%M:%S)" >> logs/screen.log
