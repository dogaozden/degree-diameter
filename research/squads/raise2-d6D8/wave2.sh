#!/bin/bash
# round-2 wave 2: k=3 orbits (ORBIT "3 2 0": S = two orbits of size 3 under an order-3 automorphism), 900 s, THREADS=1.
# Picked from screen/k3_base.tsv: psl 7 x Z95 (N 15960) min 12 p1 25 p10 76; psl 7 x Z98 (16464) min 6; sl 7 x Z49 (16464).
cd /home/user/degree-diameter/research/structured
R=/home/user/degree-diameter/research/squads/raise2-d6D8
run() { tag=$1; seed=$2; shift 2; ORBIT="3 2 0" THREADS=1 nice -n 5 timeout 1100 ./haar_sym 6 8 900 $seed 8 $R/sols_tmp/d6D8_${tag}_orb3f0_s${seed}.txt "$@" > $R/runs/d6D8_${tag}_orb3f0_s${seed}.log 2>&1; }
run psl_7_95 1 psl 7 95 &
run psl_7_95 2 psl 7 95 &
run psl_7_98 1 psl 7 98 &
run sl_7_49 1 sl 7 49 &
wait
echo WAVE2_DONE >> $R/runs/wave2.out
