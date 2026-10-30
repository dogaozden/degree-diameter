#!/bin/bash
# re-anneal the best 3 pairs: SA=1 SECS=60 SEED=2
cd /home/user/degree-diameter/research/squads/s65r5/c8
DC=/home/user/degree-diameter/research/s65/tools/dcenum
for b in sdp256_321_3_1_1 sdp256_445_2_1_1 sdp256_532_1_1_1; do
  line=$(SA=1 SECS=60 SEED=2 timeout 240 nice -n 10 $DC "keep/$b.dc2" 6 5 "keep/$b.s60.edges" 2>/dev/null | grep '^RESULT' | tail -1)
  echo "$b s60 $(echo "$line" | sed -n 's/.* best \([0-9-]*\) .*/\1/p')" >> reanneal.txt
done
echo REANNEALDONE >> reanneal.txt
