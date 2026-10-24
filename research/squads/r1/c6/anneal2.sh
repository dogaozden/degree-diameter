#!/bin/bash
# k=2 family anneal (not exhausted by RANDORB: ~1M orbit triples, 2M samples)
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r1/c6
cd $C
ORBIT="2 3 0" timeout 900 nice -n 10 $B/haar_sym 6 5 300 2 8 $C/a_sl_5_3_23_0_s2.txt sl 5 3 > $C/logs/a_sl_5_3_23_0_s2.log 2>&1
echo done
