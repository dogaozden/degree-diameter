#!/bin/bash
cd /home/user/degree-diameter/research/squads/d3D7-r1/c7
T="timeout 900 nice -n 10 ./tsa"
$T 150 1 60 2 0.05 cal150_plain.edges > logs/cal150_plain.log 2>&1
R=4 LAMBDA=0.1 $T 150 1 60 2 0.05 cal150_g4.edges > logs/cal150_g4.log 2>&1
for s in 1 2 3; do
  $T 170 $s 120 1 0.05 n170_s$s.edges > logs/n170_s$s.log 2>&1
done
R=4 LAMBDA=0.1 $T 170 4 120 1 0.05 n170_g4_s4.edges > logs/n170_g4_s4.log 2>&1
echo ALLDONE > logs/done.txt
