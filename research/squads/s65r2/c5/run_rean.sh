#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r2/c5
./reanneal.sh 260 1 2 90 > logs/rean_260.txt 2>&1
./reanneal.sh 63 1 1 90 > logs/rean_63.txt 2>&1
./reanneal.sh 261 1 1 90 > logs/rean_261.txt 2>&1
echo REAN_END > logs/rean_done.txt
