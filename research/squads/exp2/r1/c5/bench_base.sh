#!/bin/bash
# baseline: original d7hex.c, q=5, K=13 (pg23.hg), mind 4, seeds 1..3, 300 s budget per call
cd /home/user/degree-diameter/research/squads/exp2/r1/c5
for s in 1 2 3; do
  t0=$(date +%s.%N)
  timeout 900 nice -n 10 ./d7hex search hex/hex_q5.bin 0 $s 300 base_s$s.sol 3 2 4 pg23.hg > base_s$s.out 2> base_s$s.err
  t1=$(date +%s.%N)
  echo "seed $s wall $(echo "$t1 - $t0" | bc) $(grep -h RESULT base_s$s.out)" >> base_summary.txt
done
echo DONE >> base_summary.txt
