#!/bin/bash
# (14,9) on PSL(2,25)^2 (N = 60,840,000, +4.8% over the record 58,034,328): order 6 swap o conj vs order 3 conj
SP=/tmp/claude-0/-home-user-degree-diameter/a6c59fab-444e-5347-94c2-554d7c4d893d/scratchpad
B=$SP/bin/haar_order2n
cd /home/user/degree-diameter/research/theorems/order2/runs/r2
RANDORB=40 ORBIT="6 2 2" ASWAPC=1 nice -n 8 $B 14 9 10 31 8 /dev/null prod psl 25 psl 25 1 > ro149_psl25sq_k6.log 2>&1
RANDORB=40 ORBIT="3 4 2" nice -n 8 $B 14 9 10 32 8 /dev/null prod psl 25 psl 25 1 > ro149_psl25sq_k3.log 2>&1
echo done > screen149.done
