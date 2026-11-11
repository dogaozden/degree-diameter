#!/bin/bash
# short k=6 seeds on SL(2,7)^2 x Z31 at (13,8), two at a time, until one solves or the list ends
cd /tmp/claude-0/-home-user-degree-diameter/58e8cabc-b55f-55a3-910c-be10e616a47b/scratchpad/runs
for s in "$@"; do
  ORBIT="6 2 1" ASWAPC=1 AR=6 timeout 400 nice -n 5 ../src/haar_order2b 13 8 300 $s 8 /tmp/claude-0/-home-user-degree-diameter/58e8cabc-b55f-55a3-910c-be10e616a47b/scratchpad/runs/d13D8_prod_sl_7_sl_7_31_orb6swc_s$s.txt prod sl 7 sl 7 31 > an138_sl7sq_31_k6_s$s.log 2>&1
  if grep -q "^wrote" an138_sl7sq_31_k6_s$s.log; then echo "seed $s solved"; fi
done
