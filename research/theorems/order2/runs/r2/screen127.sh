#!/bin/bash
# (12,7) on SL(2,8)^2 (N = 254,016, mu ~ 118): order 6 (swap o conj, balanced involution), order 3 (conj), order 2 (swap), random.
SP=/tmp/claude-0/-home-user-degree-diameter/a6c59fab-444e-5347-94c2-554d7c4d893d/scratchpad
B=$SP/bin/haar_order2n
cd /home/user/degree-diameter/research/theorems/order2/runs/r2
RANDORB=3000 ORBIT="6 2 0" ASWAPC=1 nice -n 8 $B 12 7 10 21 8 /dev/null prod sl 8 sl 8 1 > ro127_sl8sq_k6.log 2>&1
RANDORB=3000 ORBIT="3 4 0" nice -n 8 $B 12 7 10 22 8 /dev/null prod sl 8 sl 8 1 > ro127_sl8sq_k3.log 2>&1
RANDORB=3000 ORBIT="2 6 0" ASWAPC=1 nice -n 8 $B 12 7 10 23 8 /dev/null prod sl 8 sl 8 1 > ro127_sl8sq_k2.log 2>&1
RANDSAMPLE=3000 nice -n 8 $B 12 7 10 24 8 /dev/null prod sl 8 sl 8 1 > ro127_sl8sq_rand.log 2>&1
echo done > screen127.done
