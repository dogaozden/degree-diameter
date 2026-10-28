#!/bin/bash
cd /home/user/degree-diameter/research/squads/thmfam-r1/c7
for D in 10 9; do nice -n 10 timeout 900 python3 bis.py 7 11 $D 4; done
for q in 13 17 19 23; do for D in 8 9; do nice -n 10 timeout 900 python3 bis.py 7 $q $D 4; done; done
for q in 17 29; do for D in 8 9 10; do nice -n 10 timeout 900 python3 bis.py 13 $q $D 3; done; done
