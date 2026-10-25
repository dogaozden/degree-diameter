#!/bin/bash
cd /home/user/degree-diameter/research/squads/r2_d14D8/c2
while [ ! -f q5_sa.done ]; do sleep 3; done
./eval_q5.sh > eval_q5.log 2>&1
HEX7=/home/user/degree-diameter/research/squads/cells/d14D8_work/hex/hex_q7.bin
for k in 6 7; do
  timeout 900 nice -n 10 ./bundle $HEX7 7 $k 1 400 60 7 rand h_q7_k${k}_m1.txt 2000 > log_q7_k${k}_m1.txt 2>&1
done
echo DONE > q7_sa.done
./eval_q7.sh > eval_q7.log 2>&1
echo DONE > chain.done
