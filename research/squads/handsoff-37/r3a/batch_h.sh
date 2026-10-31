#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
BIN=./symloc2 ./batch.sh cfg_h.txt
for s in 3 4 5 6 7; do
  ./run1.sh c170_D5seq 5 17 4 2,2,2,2,2,2,2,2,1 2,2,2,2,2,2,2,2,1 30 $s 40 4
done
echo SEQ_DONE
# restarts from the best n=170 graph (cost 155), group file from the same config (seed 2)
for s in 1 2; do
  ./restart.sh c170_D5rst out/t170D5/s2/grp.txt out/t170D5/s2/sa_best.edges 60 $s 8 2
done
echo BATCH_DONE
