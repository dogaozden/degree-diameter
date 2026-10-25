#!/bin/bash
# continuation: order-30 group warm-started from the 536 set, after the k=3 chain (pid 6096) exits
cd /home/user/degree-diameter/research/squads/d13D7_r7/c1
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
while kill -0 6096 2>/dev/null; do sleep 2; done
echo "start k1 continuation from 536 $(date)"
timeout 900 nice -n 10 python3 sub13.py --k 1 --start work/k1_s2_best.idx --texact 5 --theur 150 --seed 5
echo "chain3 done $(date)"
