#!/bin/bash
# (5,5) above 384: bi-coset graphs with |H| = 2 (Delta = 5) of every SmallGroup of the even orders in the list,
# SECS seconds of annealing per (group, H, K). The 384-vertex vertex-transitive graph is the bi-coset graph of
# SmallGroup(384,543) with |H| = 2 and is re-found this way in under a second.
SECS=${1:-3}; shift
for o in "$@"; do
  ./sweep_exh.sh $o 2 5 $SECS "[1..NrSmallGroups($o)]" 1
  echo "$o done $(date -u +%H:%M)" >> logs/queue55.log
done
