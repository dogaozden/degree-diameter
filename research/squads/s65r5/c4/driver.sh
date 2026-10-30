#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r5/c4
for K in $(seq 1 13); do
  now=$(date +%s); dl=$(date -d "2026-10-30 09:46:00 UTC" +%s)
  if [ "$now" -ge "$dl" ]; then echo "deadline reached before chunk $K" >> progress.txt; break; fi
  ./run_chunk.sh $K
done
echo "driver finished $(date +%T)" >> progress.txt
