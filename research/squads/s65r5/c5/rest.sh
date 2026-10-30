#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r5/c5
until grep -q "chunk 06 done" progress.txt; do sleep 5; done
for c in 07 08 09 10 11 12 13; do ./run_chunk.sh $c; done
echo "ALL CHUNKS FINISHED $(date -u +%H:%M:%S)" >> progress.txt
