#!/bin/bash
# exhaustive 2+2-base lifts over Z3^2 x|_M Z24 for (3,10) at 864 (the D=10 half of guess_affine.sh, lost in the restart)
cd "$(dirname "$0")/.."
B=bases/enum/b2_3/b2_3_0.txt
for M in "2 0 0 2" "0 2 1 0" "0 1 1 0" "0 2 1 1" "0 1 1 1" "0 2 1 2"; do timeout 2400 ./lift exhaust $B 10 sols/guess_d3D10_aff3_${M// /}_24.txt aff 3 $M 24 2>/dev/null; done
