#!/bin/bash
cd /home/user/degree-diameter/research/squads/hexfam_r3/c3
R=/home/user/degree-diameter/research/d10D7/sets/P11_r6c7_756.txt
S=/home/user/degree-diameter/research/d10D7/sets/L11_spread.txt
for cfg in "ovl 2" "ovl 3" "rand 1" "rand 2" "rand 3" "nx 1" "nxd 1"; do
  set -- $cfg
  timeout 400 nice -n 10 python3 ext_all.py 11 $R $S /home/user/degree-diameter/research/squads/hexfam_r3/c3/$1_s$2 $2 $1 40 300 > $1_s$2.log 2>&1
done
echo BATCHDONE > batch.done
