#!/bin/bash
# card c1: sweep SmallGroup(704, i), i = 1..693, in chunks of 50; no new chunk after the deadline
cd /home/user/degree-diameter/research/squads/s65r2/c1
DEADLINE=$(date -d "2026-10-30 07:53 UTC" +%s)
for start in $(seq 1 50 693); do
  end=$((start+49)); [ $end -gt 693 ] && end=693
  if [ $(date +%s) -gt $DEADLINE ]; then echo "STOP before $start.. $(date)" >> progress.txt; break; fi
  echo "START $start..$end $(date)" >> progress.txt
  timeout 1500 nice -n 10 ./sweep.sh 704 2 6 3 "[$start..$end]"
  echo "DONE $start..$end $(date)" >> progress.txt
done
echo "ALL FINISHED $(date)" >> progress.txt
