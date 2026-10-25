#!/bin/bash
# baseline: original mlift_ejoint, K33m over Z_23, m=69, 120 s CPU, seeds 1..3 (one run at a time)
cd /home/user/degree-diameter/research/squads/d12D5-r1/c6
D=/home/user/degree-diameter/research/d12D5
for s in 1 2 3; do
  INIT_ECHART=$D/graphs/d12D5_n10692_k33m_z22e_echart.txt THREADS=1 \
    timeout 1500 nice -n 10 ./mlift_ejoint_orig $D/base_k33m.txt $D/tables/z23.txt 120 $s 2.0 0.8 out/orig_s$s > logs/orig_s$s.log 2>&1
  echo "done seed $s $(date +%T)" >> logs/base_progress.txt
done
