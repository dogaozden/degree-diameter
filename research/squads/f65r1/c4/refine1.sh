#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c4
for s in 11 12 13 14 15 16; do timeout 60 nice -n 10 ./sym3 groups/G117_2_a2.txt 3 2 1 12 $s res/ref; done > refine1.txt 2>&1
echo DONE >> refine1.txt
