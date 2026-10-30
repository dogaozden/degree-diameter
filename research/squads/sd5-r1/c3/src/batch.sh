#!/bin/bash
# one process at a time (THREADS=1); 75 s per group, STAG 4000
cd /home/user/degree-diameter/research/squads/sd5-r1/c3
export TMPDIR=$PWD/tmp
for g in g360_118_A6 g360_51_SL25xC3 g420_13_A5xC7 g363_2 g364_6 g364_5 g364_1 g366_2; do
  timeout 900 nice -n 15 ./tmp/tabu data/$g.tab 7 75 data/edges_$g.txt 4000 > logs/$g.out 2> logs/$g.err
done
echo BATCH DONE > logs/batch.done
