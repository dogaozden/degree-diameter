#!/bin/bash
# (15,8) order 6 with mixed orbits 6+6+3 on SL(2,8)^2 x Z37: swap o Frobenius x->x^2, z -> 27z.  One seed per call.
# usage: launch_158.sh SEED SECONDS
SP=/tmp/claude-0/-home-user-degree-diameter/a6c59fab-444e-5347-94c2-554d7c4d893d/scratchpad
R=/home/user/degree-diameter/research/theorems/order2/runs
s=$1; secs=$2
ORBIT="6 2 0" OSUB=3 AFSWAP=1 AR=27 THREADS=1 CKPT=$R/ckpt/an158_sl8sq_37_k6sub3_s$s.ckpt BESTOUT=$R/r2/an158_sl8sq_37_k6sub3_s$s.best.txt \
  nice -n 5 $SP/bin/haar_order2 15 8 $secs $s 8 $SP/runs/d15D8_prod_sl_8_sl_8_37_orb6sub3_s$s.txt prod sl 8 sl 8 37 \
  > $R/r2/an158_sl8sq_37_k6sub3_s$s.log 2>&1
