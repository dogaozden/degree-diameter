#!/bin/bash
# (5,5) |H| = 2 bi-coset graphs of the 775 groups of order 432, exhaustive (the order skipped by queue55.sh)
cd "$(dirname "$0")"
./sweep_exh.sh 432 2 5 3 "[1..NrSmallGroups(432)]"; echo "432 done $(date -u +%H:%M)" >> logs/queue55.log
