#!/bin/bash
# c8c-smooth A/B: F15W3 schedule (COOL=15 REHEAT=30 ORBW=3 RESTARTAFTER=0, K=8) on psl 23 97, step-based clock
# (VCLOCK=0.0032 s per step = 312 steps/s = the free-core rate; MAXSTEPS=420000 ~ 60+ chains). Runs strictly one after another.
cd /home/user/degree-diameter/research/squads/handsoff-108/c8c-smooth
export ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 VCLOCK=0.0032 MAXSTEPS=420000 THREADS=1
echo "start base $(date -u +%FT%TZ)"
timeout 5400 nice -n 10 ./haar_base 10 8 100000000 108961 8 sol_base.txt psl 23 97 > ab_base.out 2> ab_base.log
echo "end base $(date -u +%FT%TZ) rc=$?"
echo "start smooth1 $(date -u +%FT%TZ)"
SMOOTHW=1 timeout 5400 nice -n 10 ./haar_smooth 10 8 100000000 108962 8 sol_s1.txt psl 23 97 > ab_s1.out 2> ab_s1.log
echo "end smooth1 $(date -u +%FT%TZ) rc=$?"
