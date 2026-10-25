#!/bin/bash
# wave 4: 90-min diagnostic runs with ORBW=3 (table-squad protocol for near misses) on the four best plateaus
cd /home/user/degree-diameter/research/structured
R=/home/user/degree-diameter/research/squads/raise-d6D8
while ! grep -q WAVE3_DONE $R/runs/wave3.out 2>/dev/null; do sleep 10; done
run() { tag=$1; seed=$2; shift 2; ORBW=3 ORBIT="2 3 0" THREADS=1 nice -n 5 timeout 5600 ./haar_sym 6 8 5400 $seed 8 $R/sols_tmp/d6D8_${tag}_orb2f0_orbw3_s${seed}.txt "$@" > $R/runs/d6D8_${tag}_orb2f0_orbw3_s${seed}.log 2>&1; }
run psl_19_5 3 psl 19 5 &
run sl_13_8 2 sl 13 8 &
run prod_sl3_sl9_1 2 prod sl 3 sl 9 1 &
run prod_psl3_sl7_4 2 prod psl 3 sl 7 4 &
wait
echo WAVE4_DONE >> $R/runs/wave4.out
