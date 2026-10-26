#!/bin/bash
# one heavy process at a time; each run 12 s
cd /home/user/degree-diameter/research/squads/b48/r1/c25
T=/home/user/degree-diameter/research/squads/b48/tools
export THREADS=1
while read base grp; do
  name=$(basename $base .txt)_$(echo $grp | tr ':' '_')
  timeout 120 nice -n 10 $T/lift $base $grp 4 8 12 7 8 runs/$name.out > runs/$name.log 2>&1
  echo "$name $(grep RESULT runs/$name.log)"
done <<LIST
bases/biaffine32.txt meta:35:2:34
bases/levi_v20_S0_1_3_8.txt meta:7:8:3
bases/levi_v24_S0_1_3_10.txt meta:23:2:22
bases/levi_v30_S0_1_3_8.txt meta:19:2:18
bases/levi_v33_S0_1_3_8.txt meta:17:2:16
bases/levi_v18_S0_1_3_7.txt meta:31:2:30
bases/levi_v15_S0_1_3_7.txt meta:37:2:36
LIST
