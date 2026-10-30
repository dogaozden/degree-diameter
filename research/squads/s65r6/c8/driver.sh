#!/bin/bash
# sweeps SmallGroup(720, i) in chunks of 40 until the deadline (no new chunk after DEADLINE, epoch seconds)
cd /home/user/degree-diameter/research/squads/s65r6/c8
start=461
while [ $start -le 840 ] && [ "$(date +%s)" -lt "$DEADLINE" ]; do
  end=$((start+39)); [ $end -gt 840 ] && end=840
  echo "chunk [$start..$end] start $(date +%T)" >> logs/driver.txt
  ./sweep.sh 720 2 6 2 "[$start..$end]" >> logs/driver.txt 2>&1
  echo "chunk [$start..$end] end $(date +%T)" >> logs/driver.txt
  start=$((end+1))
done
echo "DONE $(date +%T) next start $start" >> logs/driver.txt
