#!/bin/bash
# c3-twist driver: wait for the sl 23 x Z49 descent run to end, screen the control and twisted groups (RANDORB, a few
# seconds each), then run F15W3 descents on tpgl 23 x Z49 for 40 minutes. One heavy process at a time.
cd /home/user/degree-diameter/research/squads/handsoff-108/c3-twist
while pgrep -f "sl23_49_sol.txt" > /dev/null; do sleep 20; done
B=./haar_csl
for g in "tpgl 11 446" "tpgl 17 122" "tpgl 13 273" "tpgl 7 1753" "sl 13 271" "sl 13 273"; do
  f=rand_$(echo $g | tr ' ' _)_n300.out
  ORBIT="3 3 1" ORBW=3 RANDORB=300 THREADS=1 nice -n 10 timeout 600 $B 10 8 1 1 8 /dev/null $g > $f 2> ${f%.out}.err
done
ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 CKPT=tpgl23_49.ckpt nice -n 10 timeout 2520 $B 10 8 2400 108411 8 tpgl23_49_sol.txt tpgl 23 49 > tpgl23_49.out 2> tpgl23_49.log
echo done > chain_runs.done
