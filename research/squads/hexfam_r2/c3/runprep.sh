#!/bin/bash
cd /home/user/degree-diameter/research/squads/hexfam_r2/c3
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
for s in A5A1 A4A2 A3A3 A3A2 D4 A4 A2^3 A2^3A1 D4A1^3; do
  n=$(echo $s | tr '^' 'p')
  timeout 600 nice -n 10 python3 -u prep.py $n $s
done
echo PREPDONE
