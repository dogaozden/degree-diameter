#!/bin/bash
# K-symmetric (order 31) annealing at q=5 for the m list given; one process at a time
cd /home/user/degree-diameter/research/squads/handsoff-108/c7b-design
for m in "$@"; do
  KFILE=runs/K_q5_p31.txt M=$m ITERS=${ITERS:-20000} TEMP0=${TEMP0:-2} TEMP1=${TEMP1:-0.05} OUT=runs/sym_q5_p31_m$m.sol SEED=$((m*131+7)) TMAX=${TMAX:-900} \
    nice -n 10 ./src/symlift hex/hex_q5.bin > runs/sym_q5_p31_m$m.out 2> runs/sym_q5_p31_m$m.log
  echo "m=$m $(cat runs/sym_q5_p31_m$m.out)" >> runs/sym_q5_summary.txt
done
