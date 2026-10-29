#!/bin/bash
# (5,5): N = 2|G|/h in 356..410
./run_group.sh psl2_13 "PSL(2,13)" 6 5
./run_group.sh pgl2_13 "PGL(2,13)" 12 5
./run_group.sh psl2_19 "PSL(2,19)" 18 5
./run_group.sh psl2_17 "PSL(2,17)" 12 5
./run_group.sh pgl2_19 "PGL(2,19)" 36 5
# (7,5): N in 1154..1400
./run_group.sh psl2_17 "PSL(2,17)" 4 7
./run_group.sh pgl2_17 "PGL(2,17)" 8 7
./run_group.sh a7 "AlternatingGroup(7)" 4 7
./run_group.sh s7 "SymmetricGroup(7)" 8 7
./run_group.sh psl3_3 "PSL(3,3)" 9 7
./run_group.sh psl2_16 "PSL(2,16)" 6 7
./run_group.sh psl2_25 "PSL(2,25)" 12 7
./run_group.sh psu3_3 "PSU(3,3)" 9 7
./run_group.sh psl2_29 "PSL(2,29)" 20 7
./run_group.sh psl2_31 "PSL(2,31)" 24 7
./run_group.sh m11 "MathieuGroup(11)" 12 7
echo BATCH1_DONE
