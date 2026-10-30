#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r2/c3
for f in sg720_439_1_1 sg720_416_1_1 sg720_427_2_2; do
  echo "START $f $(date +%T)" >> logs/reanneal.txt
  SA=1 SECS=120 SEED=2 timeout 1200 nice -n 10 ./dcenum reexp/$f.dc2 6 5 reexp/${f}_best.edges > reexp/${f}.out 2>&1
  tail -1 reexp/${f}.out >> logs/reanneal.txt
  echo "DONE $f $(date +%T)" >> logs/reanneal.txt
done
echo "END $(date +%T)" >> logs/reanneal.txt
