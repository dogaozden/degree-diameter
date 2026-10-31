#!/bin/bash
# c3b driver: one heavy process at a time, in order.
# 1. F15W3 descents on sl 23 x Z49 (ORBW=3), 67 min.
# 2. ORBW=2 and ORBW=4 descents, 20 min each (same seeds family, own CKPT).
# 3. RANDORB=1000 screens on sl q x Z_n groups listed in screen_list.txt (one process each).
cd /home/user/degree-diameter/research/squads/handsoff-108/c3b-sl23x49
B=/home/user/degree-diameter/research/d10D8/sym2/haar_sym2
ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 THREADS=1 CKPT=d1.ckpt nice -n 10 timeout 4300 $B 10 8 4000 108451 8 d1.txt sl 23 49 > d1.out 2> d1.log
ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=2 THREADS=1 CKPT=d2.ckpt nice -n 10 timeout 1300 $B 10 8 1200 108452 8 d2.txt sl 23 49 > d2.out 2> d2.log
ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=4 THREADS=1 CKPT=d3.ckpt nice -n 10 timeout 1300 $B 10 8 1200 108453 8 d3.txt sl 23 49 > d3.out 2> d3.log
echo done > driver.done
