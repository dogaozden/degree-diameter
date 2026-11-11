#!/bin/bash
# exhaustive 2+2-base lifts over field-affine-type groups for (3,9) and (3,10)
cd "$(dirname "$0")/.."
B=bases/enum/b2_3/b2_3_0.txt
for M in "2 0 0 2" "0 2 1 0" "0 1 1 0" "0 1 1 1"; do timeout 1200 ./lift exhaust $B 9 sols/guess_d3D9_aff3_${M// /}_16.txt aff 3 $M 16 2>/dev/null; done
for M in "0 0 1 1 0 0 0 1 0" "0 0 1 1 0 1 0 1 0"; do timeout 1200 ./lift exhaust $B 9 sols/guess_d3D9_aff3x2_${M// /}_21.txt aff3 2 $M 21 2>/dev/null; done
for M in "2 0 0 2" "0 2 1 0" "0 1 1 0" "0 1 1 1" "0 2 1 1" "0 1 1 2"; do timeout 1800 ./lift exhaust $B 10 sols/guess_d3D10_aff3_${M// /}_24.txt aff 3 $M 24 2>/dev/null; done
