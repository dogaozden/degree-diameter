#!/bin/bash
# round-2 wave 3: sl 7 x Z49 with ORBIT "3 2 0", four valid order-3 conjugating alphas (ALPHA = index) that have the
# lowest 5000-sample minimum (alpha_sweep_k3/sl7_49_k3_alpha.tsv); 900 s each, seed 1.
cd /home/user/degree-diameter/research/structured
R=/home/user/degree-diameter/research/squads/raise2-d6D8
run() { a=$1; ORBIT="3 2 0" ALPHA=$a THREADS=1 nice -n 5 timeout 1100 ./haar_sym 6 8 900 1 8 $R/sols_tmp/d6D8_sl_7_49_a${a}_orb3f0_s1.txt sl 7 49 > $R/runs/d6D8_sl_7_49_a${a}_orb3f0_s1.log 2>&1; }
run 120 &
run 265 &
run 141 &
run 170 &
wait
echo WAVE3_DONE >> $R/runs/wave3.out
