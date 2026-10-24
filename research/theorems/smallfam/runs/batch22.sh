#!/bin/sh
# (4,9) annealing screen over metacyclic Z_m x|_r Z_k, N = 2486..2700, fixed-point-free action of order >= 3, k <= 48
cd "$(dirname "$0")/.."
nice -n 5 python3 metascreen.py 4 9 2486 2700 --kmin 5 --kmax 48 --secs 30 --seeds 1 > runs/metascreen_d4D9.log 2>&1
