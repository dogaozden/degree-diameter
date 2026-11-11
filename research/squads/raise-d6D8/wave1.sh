#!/bin/bash
# wave 1: 15-min single-thread k=2 orbit runs on the top non-degenerate N~16k candidates
cd /home/user/degree-diameter/research/structured
R=/home/user/degree-diameter/research/squads/raise-d6D8
run() { tag=$1; shift; ORBIT="2 3 0" THREADS=1 nice -n 5 timeout 1000 ./haar_sym 6 8 900 1 8 $R/sols_tmp/d6D8_${tag}_orb2f0_s1.txt "$@" > $R/runs/d6D8_${tag}_orb2f0_s1.log 2>&1; }
run sl_7_48 sl 7 48 &
run pgl_8_32 pgl 8 32 &
run psl_13_15 psl 13 15 &
run psl_11_25 psl 11 25 &
wait
echo WAVE1_DONE
