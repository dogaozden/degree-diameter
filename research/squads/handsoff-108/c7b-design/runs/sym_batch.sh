#!/bin/bash
# K-symmetric annealing batch: lines "q P m seed" from stdin; one process at a time; schedule ITERS=${ITERS}
cd /home/user/degree-diameter/research/squads/handsoff-108/c7b-design
while read q P m seed; do
  tag=sym_q${q}_p${P}_m${m}_s${seed}
  KFILE=runs/K_q${q}_p${P}.txt M=$m ITERS=${ITERS:-8000} TEMP0=${TEMP0:-1.0} TEMP1=${TEMP1:-0.05} OUT=runs/$tag.sol SEED=$seed TMAX=${TMAX:-400} \
    nice -n 10 ./src/symlift_ea hex/hex_q$q.bin > runs/$tag.out 2> runs/$tag.log
  echo "$tag $(cat runs/$tag.out)" >> runs/sym_batch_summary.txt
done
