#!/bin/bash
# spin-off: every lift of the 2+2 base over every group of order 73..87 (n = 292..348), D = 8 ((3,8) lab record 288)
cd "$(dirname "$0")/.."
for N in $(seq 73 87); do AUT=groups/a$N.txt ./bin/liftx bases/b22.txt groups/g$N.txt 8; done > runs/spin_d3D8_b22_73_87.out
echo DONE >> runs/spin_d3D8_b22_73_87.out
