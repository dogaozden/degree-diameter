#!/bin/bash
# k=3 only (k=5 and k=6 are too large for the time box); starts after the k=1 python process (6042) exits
cd /home/user/degree-diameter/research/squads/d13D7_r7/c1
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
while kill -0 6042 2>/dev/null; do sleep 2; done
echo "start k3 $(date)"
timeout 900 nice -n 10 python3 sub13.py --k 3 --texact 5 --theur 120 --seed 3
echo "chain2 done $(date)"
