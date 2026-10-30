#!/bin/bash
# (7,5): long anneals of the |H| = 2 coset graph of SmallGroup(1206,1) (cost 14 in a short run of the slow annealer)
./sweep.sh 1206 2 7 150 "[1]" 4
echo "focus1206 done $(date -u +%H:%M)" >> logs/queue75.log
