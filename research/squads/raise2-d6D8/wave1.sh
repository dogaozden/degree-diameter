#!/bin/bash
# round-2 wave 1: 900 s annealing, ORBIT "2 3 0", seed 1, on the four best metacyclic screen candidates (screen/k2_full.tsv)
cd /home/user/degree-diameter/research/structured
R=/home/user/degree-diameter/research/squads/raise2-d6D8
run() { tag=$1; shift; ORBIT="2 3 0" THREADS=1 nice -n 5 timeout 1100 ./haar_sym 6 8 900 1 8 $R/sols_tmp/d6D8_${tag}_orb2f0_s1.txt "$@" > $R/runs/d6D8_${tag}_orb2f0_s1.log 2>&1; }
run meta_1223_13_117 meta 1223 13 117 1 &
run meta_1223_13_236 meta 1223 13 236 1 &
run meta_953_17_16 meta 953 17 16 1 &
run meta_1453_11_69 meta 1453 11 69 1 &
wait
echo WAVE1_DONE >> $R/runs/wave1.out
