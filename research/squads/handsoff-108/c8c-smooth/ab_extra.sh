#!/bin/bash
# c8c-smooth extra arm (started after ab_run.sh ends): SMOOTHW=2 on the same schedule, shorter (time budget)
cd /home/user/degree-diameter/research/squads/handsoff-108/c8c-smooth
while pgrep -f ab_run.sh > /dev/null; do sleep 20; done
export ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 VCLOCK=0.0032 MAXSTEPS=300000 THREADS=1
echo "start smooth2 $(date -u +%FT%TZ)"
SMOOTHW=2 timeout 3000 nice -n 10 ./haar_smooth 10 8 100000000 108964 8 sol_s2.txt psl 23 97 > ab_s2.out 2> ab_s2.log
echo "end smooth2 $(date -u +%FT%TZ) rc=$?"
