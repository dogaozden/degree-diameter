#!/bin/bash
# c1 (r4): after queue 1, re-run the cyclic group <d8_0> (H8_8, the 240 plateau) with another seed and more time.
C=/home/user/degree-diameter/research/squads/d14D7-r4/c1
HEAVY=/home/user/degree-diameter/research/squads/bin/heavy.sh
MAP=/home/user/degree-diameter/research/cell147/data/E11.map
ORB=/home/user/degree-diameter/research/cell147/units/orbitclique
cd $C
for i in $(seq 1 300); do grep -q QUEUE_DONE $C/queue.out 2>/dev/null && break; sleep 2; done
$HEAVY 330 $ORB $MAP $C/permH_s1_d10_0__s1_d8_0__H8_8.txt 90 7 $C/flags_H8_8_seed7.txt 2> $C/log_H8_8_seed7.txt
echo "H8_8_seed7 rc=$? $(grep '^best' $C/log_H8_8_seed7.txt)" >> $C/queue.out
echo QUEUE3_DONE >> $C/queue.out
