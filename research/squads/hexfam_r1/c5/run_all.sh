#!/bin/bash
# c5 runs: one process at a time, timeout 1200 nice -n 10
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
D=/home/user/degree-diameter/research/projects/hexagon-family/hex
S=/home/user/degree-diameter/research/d10D7/sets
C=/home/user/degree-diameter/research/squads/hexfam_r1/c5
cd "$C"
timeout 1200 nice -n 10 ./ils $D/hex_q11.bin $S/P11_r6c7_756.txt $C/runs 700 11 20 7 0 > $C/log_q11.txt 2>&1
timeout 1200 nice -n 10 ./ils $D/hex_q5.bin $S/P5_c6_72.txt $C/runs 60 5 20 7 0 > $C/log_q5.txt 2>&1
timeout 1200 nice -n 10 ./ils $D/hex_q7.bin $S/P7_c5_288.txt $C/runs 60 7 20 7 0 > $C/log_q7.txt 2>&1
timeout 1200 nice -n 10 ./ils $D/hex_q13.bin $S/P13_E7sub_E6_792.txt $C/runs 300 13 20 7 0 > $C/log_q13.txt 2>&1
echo ALLDONE > $C/done.flag
