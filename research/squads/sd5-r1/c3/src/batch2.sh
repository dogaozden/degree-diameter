#!/bin/bash
# restart of the remaining groups (batch.sh died after group 2); 50 s per group, one process at a time
cd /home/user/degree-diameter/research/squads/sd5-r1/c3
export TMPDIR=$PWD/tmp
for g in g420_13_A5xC7 g363_2 g364_6 g364_5 g364_1 g366_2; do
  timeout 200 nice -n 15 ./tmp/tabu data/$g.tab 7 50 data/edges_$g.txt 4000 > logs/$g.out 2> logs/$g.err
done
echo BATCH2 DONE > logs/batch2.done
