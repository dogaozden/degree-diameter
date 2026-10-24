#!/bin/bash
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
cd /home/user/degree-diameter/research/squads/r1/c4
ORBIT="3 4 1" timeout 900 nice -n 10 $B/haar_sym 13 5 600 1 8 r1c4_A_pgl5x49_341.txt pgl 5 49 1 > r1c4_A_pgl5x49_341.log 2>&1
echo "done A $(date +%T)"
ORBIT="3 4 1" timeout 900 nice -n 10 $B/haar_sym 13 5 600 1 8 r1c4_B_pgl4x97_341.txt pgl 4 97 > r1c4_B_pgl4x97_341.log 2>&1
echo "done B $(date +%T)"
ORBIT="4 3 1" timeout 900 nice -n 10 $B/haar_sym 13 5 600 1 8 r1c4_C_psl7x35_431.txt psl 7 35 > r1c4_C_psl7x35_431.log 2>&1
echo "done C $(date +%T)"
