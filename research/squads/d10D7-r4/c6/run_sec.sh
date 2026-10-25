#!/bin/bash
cd /home/user/degree-diameter/research/squads/d10D7-r4/c6
H=/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin
: > sec_summary.txt
for s in 1 2 3; do
  timeout 100 nice -n 10 ./ls6c $H points 15 $s SEC756_s$s - section_756.txt > SEC756_s$s.log 2>&1
  echo "elliptic756 seed $s : $(grep FOUND SEC756_s$s.log | tail -1) | $(tail -1 SEC756_s$s.log)" >> sec_summary.txt
done
for s in 1 2; do
  timeout 100 nice -n 10 ./ls6c $H points 15 $s SEC806_s$s - section_806.txt > SEC806_s$s.log 2>&1
  echo "hyperbolic806 seed $s : $(grep FOUND SEC806_s$s.log | tail -1) | $(tail -1 SEC806_s$s.log)" >> sec_summary.txt
done
echo DONE >> sec_summary.txt
