#!/bin/bash
cd /home/user/degree-diameter/research/squads/r1/c2
ORBIT="3 3 2" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 11 5 600 2 8 psl549_s2.txt psl 5 49 > psl549_s2.log 2>&1; echo EXIT $? >> psl549_s2.log
ORBIT="3 3 2" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 11 5 600 1 8 sl449_s1.txt sl 4 49 > sl449_s1.log 2>&1; echo EXIT $? >> sl449_s1.log
ORBIT="3 3 2" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 11 5 300 1 8 pgl449_s1.txt pgl 4 49 > pgl449_s1.log 2>&1; echo EXIT $? >> pgl449_s1.log
echo CHAIN_DONE > chain1.done
