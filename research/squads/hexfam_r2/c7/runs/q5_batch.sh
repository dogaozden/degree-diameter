#!/bin/bash
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd /home/user/degree-diameter/research/squads/hexfam_r2/c7
H5=/home/user/degree-diameter/research/projects/hexagon-family/hex/hex_q5.bin
nice -n 10 ./mix $H5 240 4 mixed - runs/q5mixE > runs/q5mixE.out 2> runs/q5mixE.log
nice -n 10 ./mix $H5 240 5 pure - runs/q5pureE > runs/q5pureE.out 2> runs/q5pureE.log
echo done > runs/q5_batch.done
