#!/bin/bash
# sequential queue of heavy runs (one at a time), started after the k=2 driver (pid 4412) exits
cd /home/user/degree-diameter/research/squads/d13D7_r7/c1
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
while kill -0 4412 2>/dev/null; do sleep 2; done
echo "start k1 $(date)"
timeout 900 nice -n 10 python3 sub13.py --k 1 --texact 5 --theur 150 --seed 2
echo "start k3 $(date)"
timeout 900 nice -n 10 python3 sub13.py --k 3 --texact 5 --theur 120 --seed 3
echo "start k5 $(date)"
timeout 900 nice -n 10 python3 sub13.py --k 5 --texact 5 --theur 60 --seed 4
echo "chain done $(date)"
