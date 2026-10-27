#!/bin/bash
# Haar hub graphs (d 7, D 7) of order 8581..8612 per side, for (12,7) with the 4,306 freed points
cd /home/user/degree-diameter/research/projects/hexagon-family/hubs/scan
export OMP_NUM_THREADS=1 OMP_WAIT_POLICY=passive
while read N spec; do
  tag=$(echo $spec | tr ' ' '_')
  echo "== $N $spec" >> scan.log
  timeout 300 nice -n 19 ../../tools/haar_gen3 7 7 240 1 64 h_$tag.txt $spec 2>&1 | tail -2 >> scan.log
done < specs.txt
echo DONE >> scan.log
