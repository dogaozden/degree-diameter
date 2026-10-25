#!/bin/bash
# batch 2: K33m cyclic checks (calibration at 66, seeds at 72, orders 25 and 26), starts after batch 1b
C1=/home/user/degree-diameter/research/squads/d12D5-r1/c1
B=/home/user/degree-diameter/research/d12D5
K=$B/base_k33m.txt
while ! grep -q BATCH1_DONE $C1/ceiling.txt 2>/dev/null; do sleep 3; done
$C1/run.sh $K g22_cyc 25 1
$C1/run.sh $K g24_cyc 40 2
$C1/run.sh $K g24_cyc 40 3
$C1/run.sh $K g25_cyc 40 1
$C1/run.sh $K g26_cyc 40 1
echo BATCH2_DONE >> $C1/ceiling.txt
