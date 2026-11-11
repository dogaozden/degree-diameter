#!/bin/bash
SP=/tmp/claude-0/-home-user-degree-diameter/a6c59fab-444e-5347-94c2-554d7c4d893d/scratchpad
cd /home/user/degree-diameter/research/theorems/order2/runs/r2
RANDORB=10000000 NEARDUMP=0 ORBIT="2 3 0" AR=11 nice -n 8 $SP/bin/haar_order2n 6 8 10 61 8 /dev/null psl 11 24 > ro68_psl11x24_r11_1e7.log 2>&1
RANDORB=10000000 NEARDUMP=0 ORBIT="2 3 0" AR=23 nice -n 8 $SP/bin/haar_order2n 6 8 10 62 8 /dev/null psl 11 24 > ro68_psl11x24_r23_1e7.log 2>&1
echo done > ro68_psl.done
