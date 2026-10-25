#!/bin/bash
# (13,9) order 6 at odd D on SL(2,64) x Z133 (Z7 x Z19): Frobenius x -> x^2 (order 6), z -> 65 z (order 3 mod 7,
# order 6 mod 19, so alpha^3 fixes Z7 and negates Z19: a tight involution, |Fix(alpha^3)| = 504*7, |Anti| = 520*19).
# Layout e + 6 + 6 (ORBIT="6 2 1").  usage: launch_139.sh SEED SECONDS [THREADS]
SP=/tmp/claude-0/-home-user-degree-diameter/a6c59fab-444e-5347-94c2-554d7c4d893d/scratchpad
R=/home/user/degree-diameter/research/theorems/order2/runs
s=$1; secs=$2; th=${3:-1}
ORBIT="6 2 1" AFROB=1 AR=65 THREADS=$th CKPT=$R/ckpt/an139_sl64_133_k6_s$s.ckpt BESTOUT=$R/r2/an139_sl64_133_k6_s$s.best.txt \
  nice -n 5 $SP/bin/haar_order2n 13 9 $secs $s 8 $SP/runs/d13D9_sl_64_133_orb6_s$s.txt sl 64 133 \
  > $R/r2/an139_sl64_133_k6_s$s.log 2>&1
