#!/bin/bash
# chunks of 50 ids of SmallGroup(720, i); no new chunk starts after the deadline (07:52 local)
cd /home/user/degree-diameter/research/squads/s65r2/c3
DEADLINE=$(date -d "07:52" +%s)
for lo in $(seq 1 50 840); do
  hi=$((lo+49)); [ $hi -gt 840 ] && hi=840
  if [ $(date +%s) -ge $DEADLINE ]; then echo "STOP before [$lo..$hi] $(date +%T)" >> logs/progress.txt; break; fi
  echo "START 720 [$lo..$hi] $(date +%T)" >> logs/progress.txt
  timeout 1200 nice -n 10 ./sweep.sh 720 2 6 3 "[$lo..$hi]"
  echo "DONE 720 [$lo..$hi] $(date +%T)" >> logs/progress.txt
done
echo "END $(date +%T)" >> logs/progress.txt
