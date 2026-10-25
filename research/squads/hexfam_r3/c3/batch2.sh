#!/bin/bash
cd /home/user/degree-diameter/research/squads/hexfam_r3/c3
R=/home/user/degree-diameter/research/d10D7/sets/P11_r6c7_756.txt
S=/home/user/degree-diameter/research/d10D7/sets/L11_spread.txt
for sd in 4 5 6 7; do
  timeout 400 nice -n 10 python3 ext_all.py 11 $R $S /home/user/degree-diameter/research/squads/hexfam_r3/c3/ovl_s$sd $sd ovl 40 300 > ovl_s$sd.log 2>&1
done
echo done > batch2.done
