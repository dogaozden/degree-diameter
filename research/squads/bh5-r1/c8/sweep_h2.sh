#!/bin/bash
# Sweep h=2, DEG=5 over all exported groups of orders 356..380 (2 s per group, MAXCAND 2000 per subgroup pair).
cd /home/user/degree-diameter/research/squads/bh5-r1/c8
for f in groups/s_3[5-7][0-9]_*.txt groups/s_380_*.txt; do
  b=$(basename $f .txt)
  timeout 20 nice -n 10 ./bicoset $f 2 5 2 2000 7 found_$b.edges
done
echo SWEEP_DONE
