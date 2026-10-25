#!/bin/bash
# (15,9) order 6 at odd D on SL(2,64) x Z403 (Z13 x Z31): Frobenius x -> x^2 (order 6), z -> 367 z (order 3 mod 13,
# order 6 mod 31, so alpha^3 fixes Z13 and negates Z31: a tight involution, |Fix(alpha^3)| = 504*13, |Anti| = 520*31).
# Layout 6+6+3 (OSUB=3, no fixed letter); OSTAB=1 (energy counts uncovered alpha-orbits).  usage: launch_159.sh SEED SECONDS [THREADS]
SP=/tmp/claude-0/-home-user-degree-diameter/a6c59fab-444e-5347-94c2-554d7c4d893d/scratchpad
R=/home/user/degree-diameter/research/theorems/order2/runs
s=$1; secs=$2; th=${3:-1}
OSTAB=1 ORBIT="6 2 0" OSUB=3 AFROB=1 AR=367 THREADS=$th CKPT=$R/ckpt/an159_sl64_403_k6sub3_ostab_s$s.ckpt BESTOUT=$R/r2/an159_sl64_403_k6sub3_ostab_s$s.best.txt \
  nice -n 5 $SP/bin/haar_order2n 15 9 $secs $s 8 $SP/runs/d15D9_sl_64_403_orb6sub3_ostab_s$s.txt sl 64 403 \
  > $R/r2/an159_sl64_403_k6sub3_ostab_s$s.log 2>&1
