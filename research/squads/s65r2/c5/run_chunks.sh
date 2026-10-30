#!/bin/bash
# runs chunks of 25 ids of SmallGroup(1080,i) (after the 250-275 chunk), no new chunk starts after DEADLINE
cd /home/user/degree-diameter/research/squads/s65r2/c5
DEADLINE=$(date -d "07:53" +%s)
while pgrep -f "[s]weep.sh 1080 3 6 3 \[250" >/dev/null; do sleep 5; done
for lo in $(seq 1 25 1213); do
  hi=$((lo+24)); [ $hi -gt 1213 ] && hi=1213
  if [ $lo -ge 250 ] && [ $lo -le 275 ]; then continue; fi
  if [ $(date +%s) -ge $DEADLINE ]; then echo "STOP before [$lo..$hi] $(date +%T)" >> logs/progress.txt; break; fi
  echo "START [$lo..$hi] $(date +%T)" >> logs/progress.txt
  timeout 900 nice -n 10 ./sweep.sh 1080 3 6 3 "[$lo..$hi]"
  echo "DONE [$lo..$hi] $(date +%T) lines=$(wc -l < logs/sw_1080_h3_d6.txt)" >> logs/progress.txt
done
echo "END $(date +%T)" >> logs/progress.txt
