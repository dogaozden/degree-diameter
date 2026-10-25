#!/bin/bash
# (12,7) on SL(2,64) (N = 262,080, mu ~ 154): Frobenius order 6 (involution x->x^8 balanced: |Fix| 504, |Anti| 520),
# Frobenius order 3 (x->x^4), conjugation order 3, Frobenius order 2, random.
SP=/tmp/claude-0/-home-user-degree-diameter/a6c59fab-444e-5347-94c2-554d7c4d893d/scratchpad
B=$SP/bin/haar_order2n
cd /home/user/degree-diameter/research/theorems/order2/runs/r2
RANDORB=3000 ORBIT="6 2 0" AFROB=1 nice -n 8 $B 12 7 10 41 8 /dev/null sl 64 1 > ro127_sl64_k6frob.log 2>&1
RANDORB=3000 ORBIT="3 4 0" AFROB=2 nice -n 8 $B 12 7 10 42 8 /dev/null sl 64 1 > ro127_sl64_k3frob.log 2>&1
RANDORB=3000 ORBIT="3 4 0" nice -n 8 $B 12 7 10 43 8 /dev/null sl 64 1 > ro127_sl64_k3conj.log 2>&1
RANDORB=3000 ORBIT="2 6 0" AFROB=3 nice -n 8 $B 12 7 10 44 8 /dev/null sl 64 1 > ro127_sl64_k2frob.log 2>&1
RANDSAMPLE=3000 nice -n 8 $B 12 7 10 45 8 /dev/null sl 64 1 > ro127_sl64_rand.log 2>&1
echo done > screen127b.done
