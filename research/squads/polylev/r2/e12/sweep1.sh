#!/bin/bash
E=/home/user/degree-diameter/research/squads/polylev/r2/e12
for K in 20 24 28 32; do
  echo "=== k=$K seed=1 300 CPU s ($(date +%T))"
  $E/runk.sh $K 1 300
done
echo "SWEEP1 DONE $(date +%T)"
