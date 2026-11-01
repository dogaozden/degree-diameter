#!/bin/bash
# A/B: interleaved chains in one process. Chain 1 (initial) and every odd chain: random start (arm R);
# every even chain: biased start = best of 50 random sets by C3E (collisions at distance 3, then ORBW=3 energy) (arm B).
# F15W3 schedule in steps: VCLOCK = 1/300 s per step, COOL=15, REHEAT=30 (simulated seconds).
cd /home/user/degree-diameter/research/squads/handsoff-108/c1b-structure
env ORBIT="3 3 1" ORBW=3 RESTARTAFTER=0 COOL=15 REHEAT=30 VCLOCK=0.003333 BIASN=50 BSTAT=C3E MAXSTEPS=5000000 \
  nice -n 10 timeout 5400 ./haar_c1b 10 8 100000000 108151 8 ab_best.txt psl 23 97 > ab.out 2>> ab.log
echo "exit $?" >> ab.out
