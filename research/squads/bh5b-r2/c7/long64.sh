#!/bin/sh
cd /home/user/degree-diameter/research/squads/bh5b-r2/c7
VL=/home/user/degree-diameter/research/beyond-haar-d5b/src/vl
INC=1 D=5 SECS=100 SEED=1 OUT=runs/L_b9_g52.sol timeout 200 nice -n 10 $VL bases/b9.txt grp/sg_64_52.txt > runs/L_b9_g52.out 2>runs/L_b9_g52.err
INC=1 D=5 SECS=100 SEED=2 OUT=runs/L_b9_g55.sol timeout 200 nice -n 10 $VL bases/b9.txt grp/sg_64_55.txt > runs/L_b9_g55.out 2>runs/L_b9_g55.err
echo ALLDONE > runs/long64.done
