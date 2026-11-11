#!/bin/bash
# wave 2: 20-min single-thread k=2 orbit runs on the large-Q candidates from the 15841-22000 screen
cd /home/user/degree-diameter/research/structured
R=/home/user/degree-diameter/research/squads/raise-d6D8
run() { tag=$1; seed=$2; shift 2; ORBIT="2 3 0" THREADS=1 nice -n 5 timeout 1300 ./haar_sym 6 8 1200 $seed 8 $R/sols_tmp/d6D8_${tag}_orb2f0_s${seed}.txt "$@" > $R/runs/d6D8_${tag}_orb2f0_s${seed}.log 2>&1; }
run psl_19_5 1 psl 19 5 &
run psl_19_5 2 psl 19 5 &
run sl_13_8 1 sl 13 8 &
run psl_13_16 1 psl 13 16 &
wait
echo WAVE2_DONE >> $R/runs/wave2.out
