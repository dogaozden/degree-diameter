#!/bin/bash
# (6,5) |H| = 3, 3-rich orders beyond the first list (1161 -> 774, 1215 -> 810, 1188 -> 792, 1134 -> 756 vertices)
cd "$(dirname "$0")"
for o in 1161 1215 1188 1134; do
  ./sweep_exh.sh $o 3 6 10 "[1..NrSmallGroups($o)]"; echo "$o (6,5) h3 done $(date -u +%H:%M)" >> logs/queue_h3_65.log
done
