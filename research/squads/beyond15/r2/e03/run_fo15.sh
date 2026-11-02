#!/bin/bash
# e03: exhaustive order-15 Foster lifts (foster.perm), prime n, all lambdas of order 15
E=/home/user/degree-diameter/research/squads/beyond15/r2/e03
L=/home/user/degree-diameter/research/frontier/beyond15/lsym
run() { env EXH=1 T0=2.0 T1=0.05 L=1200 THREADS=1 timeout 300 nice -n 10 /home/user/degree-diameter/research/frontier/bin/liftsym $L/foster.txt $L/foster.perm $1 $2 15 60 3 $E/out/fo$1_exh_l$2 2>&1 | tail -1; }
for lam in 4 16 38 76 85 105 128; do run 151 $lam; done
for lam in 5 25 27 29 82 114 117 145; do run 181 $lam; done
echo DONE
