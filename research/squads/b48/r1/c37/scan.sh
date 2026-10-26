#!/bin/bash
# c37 scan: affine permutation graphs, composite N, sequential, one process at a time
cd /home/user/degree-diameter/research/squads/b48/r1/c37
for N in 1094 1104 1110 1120; do
  THREADS=1 timeout 120 nice -n 10 ./aff $N 25 3 1000 60 n$N.edges
done
