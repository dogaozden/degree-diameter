#!/bin/bash
# (13,10) order 6 on SL(2,16)^2 x Z21: swap o conj(order 3), z -> 5z.  One seed per call, single thread, with checkpoint.
# usage: launch_1310.sh SEED SECONDS
SP=/tmp/claude-0/-home-user-degree-diameter/a6c59fab-444e-5347-94c2-554d7c4d893d/scratchpad
R=/home/user/degree-diameter/research/theorems/order2/runs
s=$1; secs=$2
ORBIT="6 2 1" ASWAPC=1 AR=5 THREADS=1 CKPT=$R/ckpt/an1310_sl16sq_21_k6_s$s.ckpt BESTOUT=$R/r2/an1310_sl16sq_21_k6_s$s.best.txt \
  nice -n 5 $SP/bin/haar_order2 13 10 $secs $s 8 $SP/runs/d13D10_prod_sl_16_sl_16_21_orb6swc_s$s.txt prod sl 16 sl 16 21 \
  > $R/r2/an1310_sl16sq_21_k6_s$s.log 2>&1
