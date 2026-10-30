#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r5/c3
DC=/home/user/degree-diameter/research/s65/tools/dcenum
rm -rf top; mkdir -p top
echo "reanneal export start $(date +%H:%M:%S)" >> progress.txt
timeout 200 nice -n 10 gap -q -c 'PORD:=256; IDS:=[6528,6532]; OUTDIR:="top";' c3p_export.g > gap_top.log 2>&1
echo "reanneal export done $(date +%H:%M:%S) $(ls top | tr '\n' ' ')" >> progress.txt
for p in 6528_3_3 6528_2_2 6532_1_1; do
  echo "anneal $p start $(date +%H:%M:%S)" >> progress.txt
  SA=1 SECS=60 SEED=2 timeout 100 nice -n 10 $DC top/c3p256_$p.dc2 6 5 top/c3p256_${p}_s2.edges 2>&1 | grep RESULT | sed "s/^/$p /" >> anneal.txt
  echo "anneal $p done $(date +%H:%M:%S)" >> progress.txt
done
echo "reanneal all done $(date +%H:%M:%S)" >> progress.txt
