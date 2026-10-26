#!/bin/bash
# every lift of the 2+2 cubic base over every group of order 43..64 (n = 172..256), D = 7
cd "$(dirname "$0")/.."
for N in $(seq 43 64); do ./bin/liftx bases/b22.txt groups/g$N.txt 7; done > runs/exh_b22.out
echo DONE >> runs/exh_b22.out
