#!/bin/bash
# improvement (b): hub-route terms in the proxy (d7hex_hub), same instance and seeds as bench_base.sh
cd /home/user/degree-diameter/research/squads/exp2/r1/c5
for s in 1 2 3; do
  t0=$(date +%s.%N)
  timeout 900 nice -n 10 ./d7hex_hub search hex/hex_q5.bin 0 $s 300 hub_s$s.sol 3 2 4 pg23.hg > hub_s$s.out 2> hub_s$s.err
  t1=$(date +%s.%N)
  echo "seed $s wall $(echo "$t1 - $t0" | bc) $(grep -h RESULT hub_s$s.out)" >> hub_summary.txt
done
echo DONE >> hub_summary.txt
