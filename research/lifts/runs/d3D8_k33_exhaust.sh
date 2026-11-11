#!/bin/bash
# (3,8): exhaustive search over all cyclic Z_N lifts of K_{3,3} (gauge-fixed, N^4 assignments), N = 44..60.
cd "$(dirname "$0")/.."
for N in $(seq 44 60); do
  timeout 900 ./lift exhaust bases/k33.txt 8 sols/d3D8_k33_cyc${N}_exhaust.txt cyc $N 2>/dev/null
done
