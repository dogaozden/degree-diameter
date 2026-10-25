#!/bin/bash
cd /home/user/degree-diameter/research/squads/r2_d14D8/c2
for k in 5 6 7; do
  timeout 900 nice -n 10 ./bundle /home/user/degree-diameter/research/squads/cells/d14D8_work/hex/hex_q5.bin 5 $k 1 1500 150 7 rand h_q5_k${k}_m1.txt 7812 > log_q5_k${k}_m1.txt 2>&1
done
echo DONE > q5_sa.done
