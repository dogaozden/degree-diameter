#!/bin/bash
# (6,5) |H| = 3: the groups of order 1053 not finished before the order was skipped (cost 4 found in group 34)
cd "$(dirname "$0")"
./sweep_exh.sh 1053 3 6 10 "Concatenation([4..9], [40..NrSmallGroups(1053)])"
echo "1053 rest done $(date -u +%H:%M)" >> logs/queue_h3_65.log
