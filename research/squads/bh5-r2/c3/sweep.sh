#!/bin/bash
# card c3 sweep: bsa over metacyclic (non-abelian) groups of orders 1156..1200, 15 s per group
cd /home/user/degree-diameter/research/squads/bh5-r2/c3
for f in grp2/mc_*.txt; do
  b=$(basename $f .txt)
  timeout 120 nice -n 10 ./bsa $f 15 20000 2 7 out/$b
done
echo SWEEP_DONE
