#!/bin/bash
# 60 s flift follow-up on the five best distinct groups from stage A (seed 3)
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/c3
for g in 156_9 156_1 156_7 160_1 156_17; do
  timeout 120 nice -n 10 ../../tools/flift k99.base g$g.bin 9 5 60 3 16 top/k99_g${g}_t60.volt > top/log_k99_g${g}_t60.txt 2>&1
done
# K9,9 minus 2-factor plus doubled matching, 20 s on the best group
timeout 60 nice -n 10 ../../tools/flift k99m.base g156_9.bin 9 5 20 1 16 top/k99m_g156_9_s1.volt > top/log_k99m_g156_9_s1.txt 2>&1
echo TOPDONE
