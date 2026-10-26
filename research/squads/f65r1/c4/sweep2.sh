#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c4
for f in groups/*_a*.txt groups/*_id.txt; do for b in "3 2 1" "2 2 2"; do timeout 20 nice -n 10 ./sym3 $f $b 0.5 21 res/sw; done; done > sweep2.txt 2>&1
echo DONE >> sweep2.txt
