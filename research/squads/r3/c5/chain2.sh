#!/bin/bash
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
T=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/src/research/structured/tools
D=/home/user/degree-diameter/research/squads/r3/c5
cd $D
for I in 29763 97227 10560 105600; do
  ALPHA=$I ORBIT="2 4 0" timeout 900 nice -n 10 $B/haar_sym 8 8 240 1 8 $D/s4_a$I.txt prod psl 7 sl 9 1 > s4_a$I.log 2>&1
done
python3 $T/orb_screen.py 8 8 119953 121500 "3 2 2" --bin $B/haar_sym --samples 100 --anyn --top 20 > screen_322.txt 2>&1
python3 $T/orb_screen.py 8 8 119953 121500 "2 4 0" --bin $B/haar_sym --samples 100 --anyn --top 20 > screen_240.txt 2>&1
echo CHAIN2_DONE > chain2.done
