#!/bin/bash
# (7,5) at 1210: all SmallGroup(1210, i) with |H| = 2 (the previous job's near misses were i = 12, 13, 15 and
# (C11 x C11):C15 with |H| = 3 at order 1815), fixed dcenum, SECS seconds x SEEDS per (group, H, K).
SECS=${1:-90}; SEEDS=${2:-3}
./sweep.sh 1210 2 7 $SECS "[13, 12, 15]" $SEEDS
./sweep.sh 1815 3 7 $SECS "[3]" $SEEDS
./sweep.sh 1210 2 7 $SECS "Difference([1..27], [12, 13, 15])" 1
echo "focus1210 done $(date -u +%H:%M)" >> logs/queue75.log
