#!/bin/bash
# c4: F15W3 fresh-descent runs, one heavy process at a time, 30 min each (nice 10, THREADS=1)
cd /home/user/degree-diameter/research/squads/handsoff-108/c4-groups
B=/home/user/degree-diameter/research/d10D8/sym2/haar_sym2
ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 THREADS=1 CKPT=d1.ckpt nice -n 10 timeout 1900 $B 10 8 1800 108502 8 d1.txt psl 29 49 > d1.out 2> d1.log
ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 THREADS=1 CKPT=d2.ckpt nice -n 10 timeout 1900 $B 10 8 1800 108503 8 d2.txt psl 27 61 > d2.out 2> d2.log
echo done > descents.done
